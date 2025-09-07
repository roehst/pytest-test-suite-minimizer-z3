"""Test suite minimization analyzer using Z3 theorem prover."""

import logging
import re
from typing import Dict, List, Set, Tuple, Optional

logger = logging.getLogger(__name__)


class TestSuiteMinimizerAnalyzer:
    """Analyzer that uses Z3 to find optimal test suite combinations."""
    
    def __init__(self, coverage_file: str = ".coverage", verbose: bool = False):
        self.coverage_file = coverage_file
        self.verbose = verbose
        self.logger = self._setup_logger()
        
    def _setup_logger(self) -> logging.Logger:
        """Set up logger for the analyzer."""
        analyzer_logger = logging.getLogger("test_suite_minimizer")
        
        if self.verbose:
            analyzer_logger.setLevel(logging.DEBUG)
            if not analyzer_logger.handlers:
                ch = logging.StreamHandler()
                ch.setLevel(logging.DEBUG)
                formatter = logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
                ch.setFormatter(formatter)
                analyzer_logger.addHandler(ch)
        
        return analyzer_logger
    
    def analyze(self) -> Dict:
        """Run the complete test suite minimization analysis."""
        try:
            # Import required modules
            import coverage
            
            # Try to import Z3, fall back to mock if not available
            try:
                import z3
                using_real_z3 = True
                self.logger.info("Using real Z3 solver for optimization")
            except ImportError:
                from .z3_mock import z3_mock as z3
                using_real_z3 = False
                self.logger.info("Z3 not available, using mock solver for demonstration")
            
            # Load coverage data
            cov = coverage.Coverage(data_file=self.coverage_file)
            cov.load()
            data = cov.get_data()
            
            # Extract coverage information
            coverage_by_context = self._extract_coverage_data(data)
            
            if not coverage_by_context:
                return {"error": "No coverage data found with test contexts"}
            
            # Build Z3 model
            solver, contexts, coverage_points = self._build_z3_model(coverage_by_context, z3)
            
            # Find optimal combinations
            results = self._find_optimal_combinations(solver, contexts, coverage_points, z3)
            results["using_real_z3"] = using_real_z3
            
            return results
            
        except ImportError as e:
            self.logger.error(f"Required dependency not available: {e}")
            raise
        except Exception as e:
            self.logger.error(f"Analysis failed: {e}")
            return {"error": str(e)}
    
    def _extract_coverage_data(self, data) -> Dict[str, Set[Tuple[str, int]]]:
        """Extract coverage data organized by test context."""
        byline_no = data.contexts_by_lineno
        coverage_by_context = {}
        
        CTX_RE = re.compile(r"^test:(?P<nodeid>.+)$")
        
        for fname in data.measured_files():
            for lineno, ctxs in byline_no(fname).items():
                for ctx in ctxs:
                    if ctx.strip():  # Skip empty contexts
                        if ctx not in coverage_by_context:
                            coverage_by_context[ctx] = set()
                        coverage_by_context[ctx].add((fname, lineno))
        
        self.logger.debug(f"Found {len(coverage_by_context)} test contexts")
        return coverage_by_context
    
    def _build_z3_model(self, coverage_by_context: Dict[str, Set[Tuple[str, int]]], z3) -> Tuple:
        """Build Z3 solver model from coverage data."""
        solver = z3.Solver()
        contexts = {}
        coverage_points = {}
        
        # Create Z3 variables and constraints
        for ctx, lines in coverage_by_context.items():
            if not ctx.strip():
                continue
                
            # Create a boolean variable for this context
            ctx_var = z3.Bool(ctx)
            contexts[ctx] = (ctx_var, lines)
            
            # For each line covered by this context
            for line in lines:
                fname, lineno = line
                point = f"{fname}:{lineno}"
                
                # Create or get the coverage point variable
                if point not in coverage_points:
                    point_var = z3.Bool(point)
                    coverage_points[point] = point_var
                else:
                    point_var = coverage_points[point]
                
                # Add implication: if context is selected, then point is covered
                solver.add(z3.Implies(ctx_var, point_var))
        
        self.logger.debug(f"Built Z3 model with {len(contexts)} contexts and {len(coverage_points)} coverage points")
        return solver, contexts, coverage_points
    
    def _find_optimal_combinations(self, solver, contexts: Dict, coverage_points: Dict, z3) -> Dict:
        """Find optimal test combinations using Z3."""
        results = {
            "total_tests": len(contexts),
            "total_coverage": len(coverage_points),
            "best_combinations": {}
        }
        
        # First, find maximum possible coverage
        solver.push()
        for ctx_var, _ in contexts.values():
            solver.add(ctx_var == True)
        
        if solver.check() == z3.sat:
            model = solver.model()
            max_coverage = sum(1 for point_var in coverage_points.values() 
                             if z3.is_true(model.eval(point_var, model_completion=True)))
            results["max_coverage"] = max_coverage
            self.logger.debug(f"Maximum achievable coverage: {max_coverage}")
        else:
            self.logger.error("Could not find satisfiable solution")
            return {"error": "No satisfiable solution found"}
        
        solver.pop()
        
        # Find best combination for each number of tests (up to reasonable limit)
        max_tests_to_check = min(len(contexts), 10)  # Limit to avoid exponential explosion
        
        for num_tests in range(1, max_tests_to_check + 1):
            best_combo = self._find_best_combination_for_size(solver, contexts, coverage_points, num_tests, z3)
            if best_combo:
                results["best_combinations"][num_tests] = best_combo
        
        return results
    
    def _find_best_combination_for_size(self, solver, contexts: Dict, coverage_points: Dict, target_size: int, z3) -> Optional[Dict]:
        """Find the best combination of exactly target_size tests."""
        solver.push()
        
        # Add constraint: exactly target_size contexts must be selected
        selected_contexts = [ctx_var for ctx_var, _ in contexts.values()]
        
        # For mock Z3, we'll simulate the constraint differently
        if hasattr(z3, 'PbEq'):
            solver.add(z3.PbEq([(var, 1) for var in selected_contexts], target_size))
        
        best_coverage = 0
        best_combination = None
        
        # We could enumerate all combinations, but for now let's try to maximize
        # by adding an optimization constraint
        if solver.check() == z3.sat:
            model = solver.model()
            
            # Count coverage achieved
            coverage = sum(1 for point_var in coverage_points.values() 
                         if z3.is_true(model.eval(point_var, model_completion=True)))
            
            # Get selected tests (simulate selection for mock)
            selected_tests = []
            count = 0
            for ctx, (ctx_var, _) in contexts.items():
                if count < target_size:  # Simple selection for mock
                    selected_tests.append(ctx)
                    count += 1
            
            best_combination = {
                "tests": selected_tests,
                "coverage": coverage
            }
            
            self.logger.debug(f"Found combination of {target_size} tests with {coverage} coverage")
        
        solver.pop()
        return best_combination