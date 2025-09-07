"""pytest plugin for test suite minimization using Z3 theorem prover."""

import logging
import os
from typing import Dict, List, Optional, Set, Tuple

import pytest
from _pytest.config import Config
from _pytest.config.argparsing import Parser
from _pytest.terminal import TerminalReporter

logger = logging.getLogger(__name__)


def pytest_addoption(parser: Parser) -> None:
    """Add command line options for the test suite minimizer."""
    group = parser.getgroup("test-suite-minimizer-z3")
    group.addoption(
        "--minimize-tests",
        action="store_true",
        default=False,
        help="Enable test suite minimization with Z3",
    )
    group.addoption(
        "--minimizer-output",
        action="store",
        default=None,
        help="Output file for minimization results (default: print to stdout)",
    )
    group.addoption(
        "--minimizer-verbose",
        action="store_true",
        default=False,
        help="Enable verbose output for minimization process",
    )


def pytest_configure(config: Config) -> None:
    """Configure the plugin based on command line options."""
    if config.option.minimize_tests:
        # Register our plugin to be active
        config.pluginmanager.register(TestSuiteMinimizerPlugin(config), "test_suite_minimizer")


class TestSuiteMinimizerPlugin:
    """Main plugin class for test suite minimization."""
    
    def __init__(self, config: Config):
        self.config = config
        self.enabled = config.option.minimize_tests
        self.output_file = config.option.minimizer_output
        self.verbose = config.option.minimizer_verbose
        self.coverage_data = None
        
        if self.verbose:
            logging.basicConfig(level=logging.DEBUG)
        
    def pytest_sessionfinish(self, session, exitstatus):
        """Called after whole test run finished, before returning exit status."""
        if not self.enabled:
            return
            
        # Only run minimization if tests passed and coverage was collected
        if exitstatus != 0:
            logger.warning("Tests failed, skipping minimization")
            return
            
        try:
            self._run_minimization()
        except ImportError as e:
            logger.error(f"Z3 solver not available: {e}")
            logger.error("Please install z3-solver: pip install z3-solver")
        except Exception as e:
            logger.error(f"Error during test suite minimization: {e}")
            if self.verbose:
                logger.exception("Full traceback:")

    def _run_minimization(self):
        """Run the test suite minimization analysis."""
        # Check if coverage data exists
        coverage_file = ".coverage"
        if not os.path.exists(coverage_file):
            logger.error("No coverage data found. Please run tests with --cov and --cov-context=test")
            return
            
        try:
            # Import the analyzer (this will work with or without Z3)
            from .analyzer import TestSuiteMinimizerAnalyzer
            
            analyzer = TestSuiteMinimizerAnalyzer(
                coverage_file=coverage_file,
                verbose=self.verbose
            )
            
            results = analyzer.analyze()
            self._output_results(results)
            
        except Exception as e:
            # Fall back to the basic analysis if analyzer fails
            logger.warning(f"Advanced analysis failed ({e}), falling back to basic coverage analysis")
            self._basic_coverage_analysis()
    
    def _basic_coverage_analysis(self):
        """Basic coverage analysis without Z3 optimization."""
        try:
            import coverage
            
            cov = coverage.Coverage(data_file=".coverage")
            cov.load()
            data = cov.get_data()
            
            print("\n" + "="*60)
            print("TEST SUITE MINIMIZER (Basic Mode - Z3 not available)")
            print("="*60)
            
            contexts = data.measured_contexts()
            print(f"Total test contexts found: {len(contexts)}")
            
            # Get coverage by context
            byline_no = data.contexts_by_lineno
            coverage_by_context = {}
            total_lines = 0
            
            for fname in data.measured_files():
                for lineno, ctxs in byline_no(fname).items():
                    total_lines += 1
                    for ctx in ctxs:
                        if ctx.strip():  # Skip empty contexts
                            if ctx not in coverage_by_context:
                                coverage_by_context[ctx] = set()
                            coverage_by_context[ctx].add((fname, lineno))
            
            print(f"Total measurable lines: {total_lines}")
            print(f"Contexts with coverage: {len(coverage_by_context)}")
            
            # Show coverage per test
            print("\nCoverage per test context:")
            for ctx, lines in sorted(coverage_by_context.items(), key=lambda x: len(x[1]), reverse=True):
                print(f"  {ctx}: {len(lines)} lines covered")
                
            print("\nTo get full Z3-powered optimization, install z3-solver:")
            print("  pip install z3-solver")
            
        except Exception as e:
            logger.error(f"Error in basic coverage analysis: {e}")
    
    def _output_results(self, results: Dict):
        """Output the minimization results."""
        output = self._format_results(results)
        
        if self.output_file:
            with open(self.output_file, 'w') as f:
                f.write(output)
            print(f"Minimization results written to {self.output_file}")
        else:
            print(output)
    
    def _format_results(self, results: Dict) -> str:
        """Format the results for display."""
        lines = []
        lines.append("\n" + "="*60)
        lines.append("TEST SUITE MINIMIZER RESULTS")
        lines.append("="*60)
        
        if "error" in results:
            lines.append(f"Error: {results['error']}")
            return "\n".join(lines)
        
        # Show solver information
        if results.get("using_real_z3", False):
            lines.append("✓ Using Z3 theorem prover for optimal solutions")
        else:
            lines.append("⚠ Using mock solver (install z3-solver for optimal results)")
        
        lines.append("")
        lines.append(f"Total tests analyzed: {results.get('total_tests', 0)}")
        lines.append(f"Total coverage points: {results.get('total_coverage', 0)}")
        lines.append(f"Maximum achievable coverage: {results.get('max_coverage', 0)}")
        
        if "best_combinations" in results and results["best_combinations"]:
            lines.append("\nOptimal test combinations:")
            for cost, combo_info in sorted(results["best_combinations"].items()):
                efficiency = combo_info['coverage'] / cost if cost > 0 else 0
                lines.append(f"  {cost} tests → {combo_info['coverage']} coverage points (efficiency: {efficiency:.1f}):")
                for test in combo_info["tests"]:
                    lines.append(f"    - {test}")
                lines.append("")
        else:
            lines.append("\nNo optimal combinations found.")
        
        return "\n".join(lines)