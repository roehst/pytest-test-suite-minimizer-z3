from example.app.interpreter import Add, Constant, Let, Variable
from example.app.typechecker import IntTy, typecheck


def test_typecheker():
    
    # Build an expression with type tyint
    term = Let(
        var=Variable("x"),
        value=Constant(10),
        body=Add(Variable("x"), Constant(5)),
    )
    ty = typecheck(term, ctx=[])
    assert isinstance(ty, IntTy)