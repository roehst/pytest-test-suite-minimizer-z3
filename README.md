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
4. Run tests: `pytest` (when test suite is added)

## License

This project is open source. See the license file for details.