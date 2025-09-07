"""Integration tests for the pytest plugin."""

import pytest
import os
import subprocess
import tempfile
import shutil
from pathlib import Path


class TestPluginIntegration:
    """Integration tests for the pytest plugin."""
    
    def test_plugin_loads_successfully(self):
        """Test that the plugin can be loaded by pytest."""
        result = subprocess.run([
            "python", "-m", "pytest", "--help"
        ], capture_output=True, text=True, env={
            **os.environ,
            "PYTHONPATH": "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        })
        
        # Should not error when loading the plugin
        assert result.returncode == 0
    
    def test_plugin_options_in_help(self):
        """Test that plugin options appear in pytest help."""
        result = subprocess.run([
            "python", "-m", "pytest", "-p", "pytest_test_suite_minimizer_z3.plugin", "--help"
        ], capture_output=True, text=True, env={
            **os.environ,
            "PYTHONPATH": "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        })
        
        assert result.returncode == 0
        help_output = result.stdout
        
        assert "--minimize-tests" in help_output
        assert "--minimizer-output" in help_output
        assert "--minimizer-verbose" in help_output
    
    def test_plugin_with_example_tests(self):
        """Test the plugin with the example tests in the repository."""
        # Change to the repository directory
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        
        # Run the plugin with the example tests
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            "--cov=example", "example/tests",
            "--cov-context=test",
            "--minimize-tests"
        ], capture_output=True, text=True, cwd=repo_dir, env={
            **os.environ,
            "PYTHONPATH": repo_dir
        })
        
        assert result.returncode == 0
        output = result.stdout
        
        # Check that the plugin output appears
        assert "TEST SUITE MINIMIZER RESULTS" in output
        assert "Total tests analyzed:" in output
        assert "Total coverage points:" in output
        assert "Optimal test combinations:" in output
    
    def test_plugin_with_output_file(self, temp_dir):
        """Test the plugin with output file option."""
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        output_file = os.path.join(temp_dir, "minimizer_results.txt")
        
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            "--cov=example", "example/tests",
            "--cov-context=test",
            "--minimize-tests",
            f"--minimizer-output={output_file}"
        ], capture_output=True, text=True, cwd=repo_dir, env={
            **os.environ,
            "PYTHONPATH": repo_dir
        })
        
        assert result.returncode == 0
        
        # Check that output file was created
        assert os.path.exists(output_file)
        
        # Check file contents
        with open(output_file, 'r') as f:
            content = f.read()
            assert "TEST SUITE MINIMIZER RESULTS" in content
            assert "Total tests analyzed:" in content
    
    def test_plugin_with_verbose_option(self):
        """Test the plugin with verbose option."""
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            "--cov=example", "example/tests",
            "--cov-context=test",
            "--minimize-tests",
            "--minimizer-verbose"
        ], capture_output=True, text=True, cwd=repo_dir, env={
            **os.environ,
            "PYTHONPATH": repo_dir
        })
        
        assert result.returncode == 0
        # Verbose mode should still produce results
        output = result.stdout
        assert "TEST SUITE MINIMIZER RESULTS" in output
    
    def test_plugin_without_coverage(self):
        """Test the plugin behavior when no coverage data is available."""
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        
        # Run without coverage collection
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            "example/tests",  # No --cov option
            "--minimize-tests"
        ], capture_output=True, text=True, cwd=repo_dir, env={
            **os.environ,
            "PYTHONPATH": repo_dir
        })
        
        # Tests should still pass, but minimizer should warn about no coverage
        assert result.returncode == 0
    
    def test_plugin_with_failing_tests(self):
        """Test the plugin behavior when tests fail."""
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        
        # Create a temporary test that will fail
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write('''
def test_failing():
    """A test that always fails."""
    assert False, "This test is designed to fail"
''')
            failing_test = f.name
        
        try:
            result = subprocess.run([
                "python", "-m", "pytest",
                "-p", "pytest_test_suite_minimizer_z3.plugin",
                "--cov=example", failing_test,
                "--cov-context=test",
                "--minimize-tests"
            ], capture_output=True, text=True, cwd=repo_dir, env={
                **os.environ,
                "PYTHONPATH": repo_dir
            })
            
            # Should exit with failure due to failing test
            assert result.returncode != 0
            
            # Should not run minimization
            assert "TEST SUITE MINIMIZER RESULTS" not in result.stdout
            
        finally:
            os.unlink(failing_test)
    
    def test_plugin_with_custom_test_suite(self, sample_test_files):
        """Test the plugin with a custom test suite."""
        # Run pytest on the sample test files
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            f"--cov={sample_test_files.name}", str(sample_test_files),
            "--cov-context=test",
            "--minimize-tests"
        ], capture_output=True, text=True, env={
            **os.environ,
            "PYTHONPATH": "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        })
        
        # Should run successfully
        assert result.returncode == 0
        output = result.stdout
        
        # Should produce minimizer results
        assert "TEST SUITE MINIMIZER RESULTS" in output or "TEST SUITE MINIMIZER (Basic Mode" in output


class TestPluginEdgeCases:
    """Test edge cases and error conditions."""
    
    def test_plugin_with_no_test_contexts(self, temp_dir):
        """Test behavior when coverage has no test contexts."""
        # Create coverage data without test contexts
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        
        # Create a minimal test that doesn't use test contexts
        test_file = os.path.join(temp_dir, "test_no_context.py")
        with open(test_file, 'w') as f:
            f.write('''
def test_simple():
    """A simple test."""
    assert True
''')
        
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            "--cov=pytest_test_suite_minimizer_z3", test_file,
            # Note: no --cov-context=test
            "--minimize-tests"
        ], capture_output=True, text=True, cwd=repo_dir, env={
            **os.environ,
            "PYTHONPATH": repo_dir
        })
        
        # Should handle gracefully
        assert result.returncode == 0
    
    def test_plugin_disabled_by_default(self):
        """Test that plugin is disabled by default."""
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            "--cov=example", "example/tests",
            "--cov-context=test"
            # Note: no --minimize-tests flag
        ], capture_output=True, text=True, cwd=repo_dir, env={
            **os.environ,
            "PYTHONPATH": repo_dir
        })
        
        assert result.returncode == 0
        # Should not show minimizer results when disabled
        assert "TEST SUITE MINIMIZER RESULTS" not in result.stdout
    
    def test_plugin_with_empty_coverage(self, temp_dir):
        """Test plugin behavior with empty coverage data."""
        repo_dir = "/home/runner/work/pytest-test-suite-minimizer-z3/pytest-test-suite-minimizer-z3"
        
        # Create an empty test file
        test_file = os.path.join(temp_dir, "test_empty.py")
        with open(test_file, 'w') as f:
            f.write('# Empty test file\npass\n')
        
        result = subprocess.run([
            "python", "-m", "pytest",
            "-p", "pytest_test_suite_minimizer_z3.plugin",
            "--cov=nonexistent_module", test_file,
            "--cov-context=test",
            "--minimize-tests"
        ], capture_output=True, text=True, cwd=repo_dir, env={
            **os.environ,
            "PYTHONPATH": repo_dir
        })
        
        # Should handle gracefully even with no meaningful coverage
        # pytest may return 5 (no tests collected) instead of 0, which is acceptable
        assert result.returncode in [0, 5]