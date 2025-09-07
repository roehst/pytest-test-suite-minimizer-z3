# Pytest Test Suite Minimizer with Z3

This is a pytest plugin that uses the Z3 theorem prover to minimize test suites while maintaining code coverage. It helps you find the optimal combination of tests that provide maximum coverage with minimum execution time.

## Installation

1. Clone this repository
2. Install the plugin:
   ```bash
   pip install -e .
   ```

3. For optimal results, install Z3:
   ```bash
   pip install z3-solver
   ```

## Usage

### Basic Usage

Run your tests with coverage and enable the minimizer:

```bash
pytest --cov=your_package --cov-context=test --minimize-tests
```

### Command Line Options

- `--minimize-tests`: Enable test suite minimization
- `--minimizer-output=FILE`: Save results to a file instead of printing to stdout
- `--minimizer-verbose`: Enable verbose output for debugging

### Example

```bash
# Run with verbose output
pytest --cov=example example/tests --cov-context=test --minimize-tests --minimizer-verbose

# Save results to file
pytest --cov=example example/tests --cov-context=test --minimize-tests --minimizer-output=results.txt
```

## How it Works

The plugin uses coverage.py to measure code coverage of each test case and translates the coverage information into logical constraints that can be solved by the Z3 theorem prover.

For each test case X and each line of code L, the plugin creates:
- A boolean variable representing whether test X is selected
- A boolean variable representing whether line L is covered
- An implication: if test X is selected, then all lines it covers are covered

Z3 then finds optimal combinations of tests that:
1. Maximize code coverage
2. Minimize the number of tests required
3. Provide efficiency metrics (coverage points per test)

## Example Output

```
============================================================
TEST SUITE MINIMIZER RESULTS
============================================================
✓ Using Z3 theorem prover for optimal solutions

Total tests analyzed: 5
Total coverage points: 95
Maximum achievable coverage: 95

Optimal test combinations:
  1 tests → 95 coverage points (efficiency: 95.0):
    - example/tests/test_interpreter.py::test_application|run

  2 tests → 95 coverage points (efficiency: 47.5):
    - example/tests/test_interpreter.py::test_application|run
    - example/tests/test_typechecker.py::test_typecheker|run
```

## Features

- **Intelligent Test Selection**: Uses Z3 to find mathematically optimal test combinations
- **Coverage Preservation**: Ensures that reduced test suites maintain the same coverage
- **Efficiency Metrics**: Shows coverage points per test for each combination
- **Flexible Output**: Results can be printed to console or saved to file
- **Fallback Mode**: Works without Z3 (with basic analysis) if Z3 is not installed
- **Verbose Debugging**: Detailed logging for troubleshooting

## Requirements

- Python >= 3.12
- pytest >= 8.4.2
- coverage >= 7.10.6
- pytest-cov >= 6.3.0
- z3-solver >= 4.15.3.0 (optional, but recommended for optimal results)

## Development

To contribute to this project:

1. Clone the repository
2. Install in development mode: `pip install -e .`
3. Run the example: `pytest --cov=example example/tests --cov-context=test --minimize-tests`
4. Run tests: `./run_tests.sh` or `pytest tests/`

### Test Suite

The project includes a comprehensive test suite covering:

- **Unit Tests**: Test individual components like the plugin, analyzer, and Z3 mock
- **Integration Tests**: Test the plugin working with real pytest sessions
- **Edge Case Tests**: Test error handling and boundary conditions

To run the tests:

```bash
# Run all tests
./run_tests.sh

# Run specific test categories
pytest tests/test_plugin.py -v          # Plugin functionality
pytest tests/test_analyzer.py -v        # Analyzer logic
pytest tests/test_z3_mock.py -v         # Z3 mock implementation
pytest tests/test_integration.py -v     # Integration tests

# Run with coverage
pytest tests/ --cov=pytest_test_suite_minimizer_z3 --cov-report=term-missing
```

The test suite validates:
- Command-line option registration and parsing
- Plugin activation and configuration
- Coverage data analysis (with and without Z3)
- Output formatting and file generation
- Error handling for various failure scenarios
- Integration with real pytest test runs

## Publishing to PyPI

This package is configured for publishing to PyPI. To publish a new version:

### Prerequisites

1. Install build and publishing tools:
   ```bash
   pip install build twine
   ```

2. Configure PyPI credentials (one-time setup):
   ```bash
   # For PyPI
   twine configure

   # Or set environment variables
   export TWINE_USERNAME=__token__
   export TWINE_PASSWORD=your_pypi_token
   ```

### Publishing Process

1. Update the version in `pyproject.toml` and `pytest_test_suite_minimizer_z3/__init__.py`

2. Build the distribution packages:
   ```bash
   python -m build --no-isolation
   ```

3. Check the built packages:
   ```bash
   twine check dist/*
   ```

4. Upload to PyPI (test first):
   ```bash
   # Upload to Test PyPI first
   twine upload --repository testpypi dist/*

   # If everything looks good, upload to PyPI
   twine upload dist/*
   ```

### Automated Publishing

For automated publishing via GitHub Actions, ensure you have:
- A PyPI API token stored as `PYPI_API_TOKEN` in GitHub Secrets
- Version tags following semantic versioning (e.g., `v0.1.0`)

The package includes all necessary metadata for PyPI:
- Package description and README
- Author information and license
- Project URLs (homepage, repository, issues)
- Python version requirements
- Dependencies and entry points
- Proper classifiers for discoverability

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.