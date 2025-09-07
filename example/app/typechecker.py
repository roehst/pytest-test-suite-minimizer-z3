from abc import ABC
from dataclasses import dataclass

from example.app.interpreter import (
    Term,
    Variable,
    Constant,
    Boolean,
    If,
    Add,
    Multiply,
    Let,
    Lambda,
    Application,
)


class Ty(ABC):
    pass


class IntTy(Ty):
    pass


class BoolTy(Ty):
    pass


@dataclass
class FunTy(Ty):
    param_ty: Ty
    return_ty: Ty


def typecheck(term: Term, ctx: list[tuple[str, Ty]]) -> Ty:
    if isinstance(term, Constant):
        return IntTy()
    elif isinstance(term, Boolean):
        return BoolTy()
    elif isinstance(term, Variable):
        for name, ty in reversed(ctx):
            if name == term.name:
                return ty
        raise TypeError(f"Unbound variable: {term.name}")
    elif isinstance(term, Add) or isinstance(term, Multiply):
        left_ty = typecheck(term.left, ctx)
        right_ty = typecheck(term.right, ctx)
        if not isinstance(left_ty, IntTy) or not isinstance(right_ty, IntTy):
            raise TypeError("Both operands of Add/Multiply must be Int")
        return IntTy()
    elif isinstance(term, If):
        cond_ty = typecheck(term.condition, ctx)
        if not isinstance(cond_ty, BoolTy):
            raise TypeError("Condition of If must be Bool")
        then_ty = typecheck(term.then_branch, ctx)
        else_ty = typecheck(term.else_branch, ctx)
        if type(then_ty) != type(else_ty):
            raise TypeError("Then and Else branches must have the same type")
        return then_ty
    elif isinstance(term, Let):
        value_ty = typecheck(term.value, ctx)
        new_ctx = ctx + [(term.var.name, value_ty)]
        return typecheck(term.body, new_ctx)
    elif isinstance(term, Lambda):
        param_ty = IntTy()  # Assume parameter is Int for simplicity
        new_ctx = ctx + [(term.param.name, param_ty)]
        body_ty = typecheck(term.body, new_ctx)
        return FunTy(param_ty, body_ty)
    elif isinstance(term, Application):
        func_ty = typecheck(term.function, ctx)
        arg_ty = typecheck(term.argument, ctx)
        if not isinstance(func_ty, FunTy):
            raise TypeError("Function in Application must be of function type")
        if type(func_ty.param_ty) != type(arg_ty):
            raise TypeError("Argument type does not match function parameter type")
        return func_ty.return_ty
    else:
        raise TypeError(f"Unknown term: {term}")
