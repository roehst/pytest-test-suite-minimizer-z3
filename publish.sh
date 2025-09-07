#!/bin/bash
# Publishing script for pytest-test-suite-minimizer-z3

set -e

echo "=== pytest-test-suite-minimizer-z3 Publishing Script ==="

# Check if build and twine are installed
if ! command -v python -m build &> /dev/null; then
    echo "Error: 'build' module not found. Install with: pip install build"
    exit 1
fi

if ! command -v twine &> /dev/null; then
    echo "Error: 'twine' not found. Install with: pip install twine"
    exit 1
fi

# Clean previous builds
echo "1. Cleaning previous builds..."
rm -rf dist/ build/ *.egg-info/

# Build the package
echo "2. Building package..."
python -m build --no-isolation

# Check the package
echo "3. Checking package..."
twine check dist/*

echo "4. Package built successfully!"
echo "   - Source distribution: $(ls dist/*.tar.gz)"
echo "   - Wheel distribution: $(ls dist/*.whl)"

echo ""
echo "Next steps:"
echo "  - To upload to Test PyPI: twine upload --repository testpypi dist/*"
echo "  - To upload to PyPI: twine upload dist/*"
echo ""
echo "Note: Make sure you have configured your PyPI credentials:"
echo "  - Set TWINE_USERNAME and TWINE_PASSWORD environment variables"
echo "  - Or run 'twine configure' to set up credentials"