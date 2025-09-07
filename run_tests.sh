#!/bin/bash
# Test runner script for pytest-test-suite-minimizer-z3

set -e

echo "=========================================="
echo "Running Test Suite for pytest-test-suite-minimizer-z3"
echo "=========================================="

# Set up Python path
export PYTHONPATH="$(pwd):$PYTHONPATH"

echo "1. Running unit tests..."
python -m pytest tests/test_plugin.py tests/test_analyzer.py tests/test_z3_mock.py -v

echo ""
echo "2. Running integration tests..."
python -m pytest tests/test_integration.py -v

echo ""
echo "3. Running all tests with coverage..."
python -m pytest tests/ --cov=pytest_test_suite_minimizer_z3 --cov-report=term-missing

echo ""
echo "4. Testing plugin functionality with example..."
python -m pytest -p pytest_test_suite_minimizer_z3.plugin --cov=example example/tests --cov-context=test --minimize-tests

echo ""
echo "=========================================="
echo "All tests completed successfully!"
echo "=========================================="