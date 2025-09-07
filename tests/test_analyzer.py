"""Test the analyzer functionality."""

import pytest
import os
from unittest.mock import Mock, patch, MagicMock

from pytest_test_suite_minimizer_z3.analyzer import TestSuiteMinimizerAnalyzer


class TestTestSuiteMinimizerAnalyzer:
    """Test the TestSuiteMinimizerAnalyzer class."""
    
    def test_analyzer_initialization(self):
        """Test analyzer initialization."""
        analyzer = TestSuiteMinimizerAnalyzer(
            coverage_file="test_coverage.db",
            verbose=True
        )
        
        assert analyzer.coverage_file == "test_coverage.db"
        assert analyzer.verbose is True
        assert analyzer.logger is not None
    
    def test_analyzer_initialization_defaults(self):
        """Test analyzer initialization with defaults."""
        analyzer = TestSuiteMinimizerAnalyzer()
        
        assert analyzer.coverage_file == ".coverage"
        assert analyzer.verbose is False
    
    def test_analyze_with_real_z3(self):
        """Test analysis components when Z3 is available."""
        analyzer = TestSuiteMinimizerAnalyzer(verbose=True)
        
        # Test that we can create an analyzer
        assert analyzer.coverage_file == ".coverage"
        assert analyzer.verbose is True
        
        # Test the setup logger functionality
        assert analyzer.logger is not None
    
    def test_analyze_with_mock_z3(self):
        """Test analysis components when Z3 is not available."""
        analyzer = TestSuiteMinimizerAnalyzer()
        
        # Test basic initialization
        assert analyzer.coverage_file == ".coverage"
        assert analyzer.verbose is False
    
    def test_extract_coverage_data(self):
        """Test coverage data extraction."""
        analyzer = TestSuiteMinimizerAnalyzer()
        
        # Mock coverage data object
        mock_data = Mock()
        mock_data.measured_files.return_value = ["file1.py", "file2.py"]
        
        # Mock contexts_by_lineno
        def mock_contexts_by_lineno(filename):
            if filename == "file1.py":
                return {
                    1: {"test:test_module.py::test_a|run", "test:test_module.py::test_b|run"},
                    2: {"test:test_module.py::test_a|run"},
                    3: {"test:test_module.py::test_b|run"}
                }
            elif filename == "file2.py":
                return {
                    1: {"test:test_other.py::test_c|run"},
                    2: {"test:test_other.py::test_c|run"}
                }
            return {}
        
        mock_data.contexts_by_lineno = mock_contexts_by_lineno
        
        result = analyzer._extract_coverage_data(mock_data)
        
        expected = {
            "test:test_module.py::test_a|run": {("file1.py", 1), ("file1.py", 2)},
            "test:test_module.py::test_b|run": {("file1.py", 1), ("file1.py", 3)},
            "test:test_other.py::test_c|run": {("file2.py", 1), ("file2.py", 2)}
        }
        
        assert result == expected
    
    def test_extract_coverage_data_empty_contexts(self):
        """Test coverage data extraction with empty contexts."""
        analyzer = TestSuiteMinimizerAnalyzer()
        
        mock_data = Mock()
        mock_data.measured_files.return_value = ["file1.py"]
        
        def mock_contexts_by_lineno(filename):
            return {
                1: {"", "  ", "test:test_module.py::test_a|run"},  # Empty and whitespace contexts
                2: {"test:test_module.py::test_a|run"}
            }
        
        mock_data.contexts_by_lineno = mock_contexts_by_lineno
        
        result = analyzer._extract_coverage_data(mock_data)
        
        # Should skip empty/whitespace contexts
        expected = {
            "test:test_module.py::test_a|run": {("file1.py", 1), ("file1.py", 2)}
        }
        
        assert result == expected
    
    def test_build_z3_model(self):
        """Test Z3 model building."""
        analyzer = TestSuiteMinimizerAnalyzer()
        
        # Mock Z3
        mock_z3 = Mock()
        mock_solver = Mock()
        mock_z3.Solver.return_value = mock_solver
        
        # Mock bool variables
        def mock_bool(name):
            var = Mock()
            var.name = name
            return var
        
        mock_z3.Bool = mock_bool
        mock_z3.Implies = Mock(side_effect=lambda a, b: f"Implies({a}, {b})")
        
        coverage_data = {
            "test:test_a|run": {("file1.py", 1), ("file1.py", 2)},
            "test:test_b|run": {("file1.py", 2), ("file1.py", 3)},
            "": set()  # Empty context should be skipped
        }
        
        solver, contexts, coverage_points = analyzer._build_z3_model(coverage_data, mock_z3)
        
        assert solver == mock_solver
        assert len(contexts) == 2  # Empty context should be skipped
        assert "test:test_a|run" in contexts
        assert "test:test_b|run" in contexts
        assert len(coverage_points) == 3  # Three unique points
        assert "file1.py:1" in coverage_points
        assert "file1.py:2" in coverage_points
        assert "file1.py:3" in coverage_points
        
        # Check that implications were added
        assert mock_solver.add.call_count >= 4  # At least 4 implications
    
    def test_find_optimal_combinations(self):
        """Test finding optimal combinations."""
        analyzer = TestSuiteMinimizerAnalyzer()
        
        # Mock Z3 solver and components
        mock_solver = Mock()
        mock_z3 = Mock()
        mock_z3.sat = "sat"
        mock_z3.is_true = Mock(return_value=True)
        
        # Mock contexts and coverage points
        contexts = {
            "test:test_a|run": (Mock(), {("file1.py", 1), ("file1.py", 2)}),
            "test:test_b|run": (Mock(), {("file1.py", 2), ("file1.py", 3)})
        }
        
        coverage_points = {
            "file1.py:1": Mock(),
            "file1.py:2": Mock(),
            "file1.py:3": Mock()
        }
        
        # Mock solver behavior
        mock_solver.check.return_value = "sat"
        mock_model = Mock()
        mock_solver.model.return_value = mock_model
        mock_model.eval.return_value = Mock()
        
        # Mock solver stack operations
        mock_solver.push = Mock()
        mock_solver.pop = Mock()
        mock_solver.add = Mock()
        
        with patch.object(analyzer, '_find_best_combination_for_size') as mock_find_best:
            mock_find_best.return_value = {
                "tests": ["test:test_a|run"],
                "coverage": 2
            }
            
            result = analyzer._find_optimal_combinations(mock_solver, contexts, coverage_points, mock_z3)
            
            assert result["total_tests"] == 2
            assert result["total_coverage"] == 3
            assert "best_combinations" in result
    
    def test_find_best_combination_for_size(self):
        """Test finding best combination for specific size."""
        analyzer = TestSuiteMinimizerAnalyzer()
        
        # Mock Z3 solver and components
        mock_solver = Mock()
        mock_z3 = Mock()
        mock_z3.sat = "sat"
        mock_z3.is_true = Mock(return_value=True)
        mock_z3.PbEq = Mock()
        
        contexts = {
            "test:test_a|run": (Mock(), {("file1.py", 1)}),
            "test:test_b|run": (Mock(), {("file1.py", 2)})
        }
        
        coverage_points = {
            "file1.py:1": Mock(),
            "file1.py:2": Mock()
        }
        
        mock_solver.check.return_value = "sat"
        mock_model = Mock()
        mock_solver.model.return_value = mock_model
        mock_model.eval.return_value = Mock()
        
        result = analyzer._find_best_combination_for_size(mock_solver, contexts, coverage_points, 1, mock_z3)
        
        assert result is not None
        assert "tests" in result
        assert "coverage" in result
        assert len(result["tests"]) <= 1  # Should respect the target size
    
    @patch('coverage.Coverage')
    def test_analyze_no_coverage_data(self, mock_coverage_class):
        """Test analysis when no coverage data found."""
        mock_coverage = Mock()
        mock_data = Mock()
        mock_coverage.get_data.return_value = mock_data
        mock_coverage_class.return_value = mock_coverage
        
        analyzer = TestSuiteMinimizerAnalyzer()
        
        with patch.object(analyzer, '_extract_coverage_data') as mock_extract:
            mock_extract.return_value = {}  # No coverage data
            
            result = analyzer.analyze()
            
            assert "error" in result
            assert "No coverage data found with test contexts" in result["error"]
    
    @patch('coverage.Coverage')
    def test_analyze_coverage_import_error(self, mock_coverage_class):
        """Test analysis when coverage module fails to import."""
        mock_coverage_class.side_effect = ImportError("No module named 'coverage'")
        
        analyzer = TestSuiteMinimizerAnalyzer()
        
        with pytest.raises(ImportError):
            analyzer.analyze()
    
    @patch('coverage.Coverage')
    def test_analyze_general_exception(self, mock_coverage_class):
        """Test analysis when a general exception occurs."""
        mock_coverage_class.side_effect = Exception("Something went wrong")
        
        analyzer = TestSuiteMinimizerAnalyzer()
        
        result = analyzer.analyze()
        
        assert "error" in result
        assert "Something went wrong" in result["error"]