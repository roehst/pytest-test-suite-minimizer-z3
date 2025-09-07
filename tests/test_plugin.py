"""Test the main plugin functionality."""

import pytest
import os
from unittest.mock import Mock, patch, MagicMock

from pytest_test_suite_minimizer_z3.plugin import (
    pytest_addoption,
    pytest_configure,
    TestSuiteMinimizerPlugin
)
from tests.conftest import MockPytestConfig, MockSession


class TestPytestAddoption:
    """Test the pytest_addoption hook."""
    
    def test_adds_minimize_tests_option(self):
        """Test that --minimize-tests option is added."""
        mock_parser = Mock()
        mock_group = Mock()
        mock_parser.getgroup.return_value = mock_group
        
        pytest_addoption(mock_parser)
        
        mock_parser.getgroup.assert_called_once_with("test-suite-minimizer-z3")
        
        # Check that addoption was called with correct parameters
        calls = mock_group.addoption.call_args_list
        assert len(calls) == 3
        
        # Check --minimize-tests option
        minimize_call = calls[0]
        assert minimize_call[0][0] == "--minimize-tests"
        assert minimize_call[1]["action"] == "store_true"
        assert minimize_call[1]["default"] is False
        
        # Check --minimizer-output option
        output_call = calls[1] 
        assert output_call[0][0] == "--minimizer-output"
        assert output_call[1]["action"] == "store"
        assert output_call[1]["default"] is None
        
        # Check --minimizer-verbose option
        verbose_call = calls[2]
        assert verbose_call[0][0] == "--minimizer-verbose"
        assert verbose_call[1]["action"] == "store_true"
        assert verbose_call[1]["default"] is False


class TestPytestConfigure:
    """Test the pytest_configure hook."""
    
    def test_registers_plugin_when_enabled(self):
        """Test that plugin is registered when --minimize-tests is used."""
        config = MockPytestConfig(minimize_tests=True)
        
        pytest_configure(config)
        
        assert len(config.pluginmanager.registered_plugins) == 1
        plugin, name = config.pluginmanager.registered_plugins[0]
        assert isinstance(plugin, TestSuiteMinimizerPlugin)
        assert name == "test_suite_minimizer"
    
    def test_does_not_register_plugin_when_disabled(self):
        """Test that plugin is not registered when --minimize-tests is not used."""
        config = MockPytestConfig(minimize_tests=False)
        
        pytest_configure(config)
        
        assert len(config.pluginmanager.registered_plugins) == 0


class TestTestSuiteMinimizerPlugin:
    """Test the main plugin class."""
    
    def test_plugin_initialization(self):
        """Test plugin initialization with different configurations."""
        # Test default configuration
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        
        assert plugin.enabled is True
        assert plugin.output_file is None
        assert plugin.verbose is False
        assert plugin.config is config
    
    def test_plugin_initialization_with_options(self):
        """Test plugin initialization with all options set."""
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output="results.txt",
            minimizer_verbose=True
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        
        assert plugin.enabled is True
        assert plugin.output_file == "results.txt"
        assert plugin.verbose is True
    
    def test_pytest_sessionfinish_disabled_plugin(self):
        """Test sessionfinish when plugin is disabled."""
        config = MockPytestConfig(
            minimize_tests=False,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        session = MockSession()
        
        # Should do nothing when disabled
        result = plugin.pytest_sessionfinish(session, 0)
        assert result is None
    
    def test_pytest_sessionfinish_failed_tests(self):
        """Test sessionfinish when tests failed."""
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        session = MockSession()
        
        # Should skip minimization when tests failed
        with patch('pytest_test_suite_minimizer_z3.plugin.logger') as mock_logger:
            plugin.pytest_sessionfinish(session, 1)  # Non-zero exit status
            mock_logger.warning.assert_called_once_with("Tests failed, skipping minimization")
    
    @patch('os.path.exists')
    def test_pytest_sessionfinish_no_coverage_data(self, mock_exists):
        """Test sessionfinish when no coverage data exists."""
        mock_exists.return_value = False
        
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        session = MockSession()
        
        with patch('pytest_test_suite_minimizer_z3.plugin.logger') as mock_logger:
            plugin.pytest_sessionfinish(session, 0)
            mock_logger.error.assert_called_once_with(
                "No coverage data found. Please run tests with --cov and --cov-context=test"
            )
    
    @patch('os.path.exists')
    def test_pytest_sessionfinish_successful_analysis(self, mock_exists):
        """Test successful analysis run."""
        mock_exists.return_value = True
        
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        session = MockSession()
        
        # Mock the analyzer import and creation
        mock_results = {
            "total_tests": 3,
            "total_coverage": 10,
            "max_coverage": 10,
            "best_combinations": {
                1: {"tests": ["test1"], "coverage": 8},
                2: {"tests": ["test1", "test2"], "coverage": 10}
            }
        }
        
        with patch('builtins.print') as mock_print:
            with patch.object(plugin, '_run_minimization') as mock_run:
                plugin.pytest_sessionfinish(session, 0)
                mock_run.assert_called_once()
    
    @patch('os.path.exists')
    def test_pytest_sessionfinish_with_output_file(self, mock_exists, temp_dir):
        """Test analysis with output file."""
        mock_exists.return_value = True
        
        output_file = os.path.join(temp_dir, "results.txt")
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=output_file,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        session = MockSession()
        
        with patch('builtins.print') as mock_print:
            with patch.object(plugin, '_run_minimization') as mock_run:
                plugin.pytest_sessionfinish(session, 0)
                mock_run.assert_called_once()
    
    @patch('os.path.exists')
    def test_basic_coverage_analysis_fallback(self, mock_exists):
        """Test fallback to basic coverage analysis."""
        mock_exists.return_value = True
        
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        session = MockSession()
        
        # Mock analyzer to raise an exception during import
        with patch.object(plugin, '_run_minimization') as mock_run:
            mock_run.side_effect = Exception("Analyzer failed")
            
            # Should not raise an exception
            plugin.pytest_sessionfinish(session, 0)
    
    def test_format_results_with_error(self):
        """Test result formatting when there's an error."""
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        results = {"error": "Something went wrong"}
        
        formatted = plugin._format_results(results)
        
        assert "TEST SUITE MINIMIZER RESULTS" in formatted
        assert "Error: Something went wrong" in formatted
    
    def test_format_results_success(self):
        """Test result formatting with successful results."""
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        results = {
            "using_real_z3": True,
            "total_tests": 5,
            "total_coverage": 20,
            "max_coverage": 20,
            "best_combinations": {
                1: {"tests": ["test_a"], "coverage": 15},
                2: {"tests": ["test_a", "test_b"], "coverage": 20}
            }
        }
        
        formatted = plugin._format_results(results)
        
        assert "✓ Using Z3 theorem prover for optimal solutions" in formatted
        assert "Total tests analyzed: 5" in formatted
        assert "Total coverage points: 20" in formatted
        assert "Maximum achievable coverage: 20" in formatted
        assert "1 tests → 15 coverage points (efficiency: 15.0)" in formatted
        assert "2 tests → 20 coverage points (efficiency: 10.0)" in formatted
        assert "- test_a" in formatted
        assert "- test_b" in formatted
    
    def test_format_results_with_mock_z3(self):
        """Test result formatting when using mock Z3."""
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        results = {
            "using_real_z3": False,
            "total_tests": 3,
            "total_coverage": 10,
            "max_coverage": 10
        }
        
        formatted = plugin._format_results(results)
        
        assert "⚠ Using mock solver (install z3-solver for optimal results)" in formatted
    
    def test_format_results_no_combinations(self):
        """Test result formatting when no combinations found."""
        config = MockPytestConfig(
            minimize_tests=True,
            minimizer_output=None,
            minimizer_verbose=False
        )
        
        plugin = TestSuiteMinimizerPlugin(config)
        results = {
            "using_real_z3": True,
            "total_tests": 0,
            "total_coverage": 0,
            "max_coverage": 0,
            "best_combinations": {}
        }
        
        formatted = plugin._format_results(results)
        
        assert "No optimal combinations found." in formatted