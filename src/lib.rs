use std::vec::IntoIter;

#[derive(Debug, Clone)]
pub enum Ast {
    Str(&'static str),
    Var(&'static str),
    Pinned(&'static str),
    Binding(&'static str),
    Block(Vec<Ast>),
    Call(Box<Ast>, Vec<Ast>),
}

#[derive(Debug, Clone, Default)]
pub struct Ctx {
    pub active_bindings: Vec<&'static str>,
    pub all_bindings: Vec<&'static str>,
    pub vars: Vec<&'static str>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(usize),
    Str(&'static str),
    Abs(Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

pub fn abs(body: Expr) -> Expr {
    Expr::Abs(Box::new(body))
}

pub fn app(f: Expr, arg: Expr) -> Expr {
    Expr::App(Box::new(f), Box::new(arg))
}

fn resolve_var(v: &str, ctx: &Ctx) -> Option<usize> {
    ctx.vars.iter().rev().position(|x| *x == v)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MacroType {
    Inline,
    Enclosing,
}

fn macro_type(args: &[Ast]) -> Option<MacroType> {
    if args.iter().any(|x| matches!(x, Ast::Block(_))) {
        Some(MacroType::Inline)
    } else if args.iter().any(|x| has_bindings(MacroType::Enclosing, x)) {
        Some(MacroType::Enclosing)
    } else {
        None
    }
}

fn has_bindings(ty: MacroType, ast: &Ast) -> bool {
    match ast {
        Ast::Binding(_) => true,
        Ast::Var(_) if ty == MacroType::Inline => true,
        Ast::Str(_) | Ast::Var(_) | Ast::Pinned(_) | Ast::Block(_) => false,
        Ast::Call(f, _) if has_bindings(ty, f) => true,
        Ast::Call(_, args) => args.iter().any(|arg| has_bindings(ty, arg)),
    }
}

fn desugar_builtin(ty: MacroType, ast: Ast, ctx: &mut Ctx) -> Result<Expr, &'static str> {
    match ast {
        Ast::Var(v) if ty == MacroType::Inline => {
            ctx.active_bindings.push(v);
            desugar(Ast::Binding(v), ctx)
        }
        Ast::Pinned(v) => match ty {
            MacroType::Inline => desugar(Ast::Var(v), ctx),
            MacroType::Enclosing => Err(v),
        },
        Ast::Binding(v) => {
            if ty == MacroType::Inline {
                ctx.all_bindings.push(v);
            }
            ctx.active_bindings.push(v);
            desugar(ast, ctx)
        }
        _ => desugar(ast, ctx),
    }
}

fn desugar_macro(ty: MacroType, ast: Ast, ctx: &mut Ctx) -> Result<Expr, &'static str> {
    fn desug_all(ty: MacroType, xs: Vec<Ast>, ctx: &mut Ctx) -> Result<Vec<Expr>, &'static str> {
        xs.into_iter().map(|x| desugar_macro(ty, x, ctx)).collect()
    }
    match ast {
        Ast::Call(f, args) if has_bindings(ty, &ast) => {
            let f = desugar_macro(ty, *f, ctx)?;
            let args = desug_all(ty, args, ctx)?;
            let list = args.into_iter().fold(Expr::Str("Nil"), |l, x| app(l, x));
            Ok(app(app(Expr::Str("Call"), f), list))
        }
        Ast::Var(v) => match ty {
            MacroType::Inline => {
                ctx.active_bindings.push(v);
                Ok(app(Expr::Str("Binding"), desugar(Ast::Binding(v), ctx)?))
            }
            MacroType::Enclosing => Ok(app(Expr::Str("Value"), desugar(ast, ctx)?)),
        },
        Ast::Pinned(v) => match ty {
            MacroType::Inline => Ok(app(Expr::Str("Value"), desugar(Ast::Var(v), ctx)?)),
            MacroType::Enclosing => Err(v),
        },
        Ast::Binding(v) => {
            if ty == MacroType::Inline {
                ctx.all_bindings.push(v);
            }
            ctx.active_bindings.push(v);
            Ok(app(Expr::Str("Binding"), desugar(ast, ctx)?))
        }
        Ast::Str(_) | Ast::Call(_, _) => Ok(app(Expr::Str("Value"), desugar(ast, ctx)?)),
        Ast::Block(_) => desugar(ast, ctx),
    }
}

fn desugar_item(x: Ast, mut xs: IntoIter<Ast>, ctx: &mut Ctx) -> Result<Expr, &'static str> {
    if ctx.active_bindings.is_empty() {
        ctx.active_bindings.push("");
    }
    let bindings = ctx.active_bindings.len();
    ctx.vars.extend(ctx.active_bindings.drain(..));
    let mut x = desugar(x, ctx)?;
    if let Some(y) = xs.next() {
        let side_effect = ctx.active_bindings.is_empty();
        let y = desugar_item(y, xs, ctx)?;
        x = if side_effect { app(y, x) } else { app(x, y) }
    }
    ctx.vars.truncate(ctx.vars.len() - bindings);
    Ok((0..bindings).fold(x, |x, _| abs(x)))
}

pub fn desugar(ast: Ast, ctx: &mut Ctx) -> Result<Expr, &'static str> {
    match ast {
        Ast::Str(s) => Ok(Expr::Str(s)),
        Ast::Var(v) => match resolve_var(&v, ctx) {
            Some(v) => Ok(Expr::Var(v)),
            None => match v {
                "=" => Ok(abs(abs(abs(app(Expr::Var(0), Expr::Var(1)))))),
                "=>" => Ok(abs(abs(Expr::Var(0)))),
                _ => Err(v),
            },
        },
        Ast::Pinned(v) => Err(v),
        Ast::Binding(name) => Ok(Expr::Str(name)),
        Ast::Block(items) => {
            let mut xs = items.into_iter();
            desugar_item(xs.next().unwrap_or(Ast::Str("Nil")), xs, ctx)
        }
        Ast::Call(f, args) => {
            let mut f = desugar(*f, ctx)?;
            let is_builtin = matches!(f, Expr::Abs(_));
            let macro_type = macro_type(&args);
            if let Some(MacroType::Inline) = macro_type {
                ctx.all_bindings = ctx.active_bindings.clone();
            }
            if args.is_empty() {
                f = app(f, Expr::Str("Nil"));
            }
            for x in args {
                f = match (macro_type, is_builtin) {
                    (None, _) => app(f, desugar(x, ctx)?),
                    (Some(ty), true) => app(f, desugar_builtin(ty, x, ctx)?),
                    (Some(ty), false) => app(f, desugar_macro(ty, x, ctx)?),
                }
            }
            if let Some(MacroType::Inline) = macro_type {
                ctx.active_bindings = ctx.all_bindings.drain(..).collect();
            }
            Ok(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Ast, Ctx, Expr, abs, app, desugar};

    #[test]
    fn lambda_app() {
        // (x => { f(x) })("foo")

        let block = Ast::Block(vec![Ast::Call(Ast::Var("f").into(), vec![Ast::Var("x")])]);
        let lambda = Ast::Call(Ast::Var("=>").into(), vec![Ast::Var("x"), block]);
        let foo = Ast::Str("foo");
        let ast = Ast::Call(lambda.into(), vec![foo]);

        let block = abs(app(Expr::Var(1), Expr::Var(0)));
        let fat_arrow = abs(abs(Expr::Var(0)));
        let lambda = app(app(fat_arrow, Expr::Str("x")), block);
        let expected = app(lambda, Expr::Str("foo"));

        let mut ctx = Ctx::default();
        ctx.vars.push("f");
        assert_eq!(desugar(ast, &mut ctx).unwrap(), expected);
    }

    #[test]
    fn let_var_in_inner() {
        // { :x = "foo", let(y, ^x, { f(y) }) }
        let x_eq_foo = Ast::Call(Ast::Var("=").into(), vec![Ast::Binding("x"), Ast::Str("foo")]);
        let f_y = Ast::Call(Ast::Var("f").into(), vec![Ast::Var("y")]);
        let let_y_x_block = Ast::Call(
            Ast::Var("let").into(),
            vec![Ast::Var("y"), Ast::Pinned("x"), Ast::Block(vec![f_y])],
        );

        let ast = Ast::Block(vec![x_eq_foo, let_y_x_block]);

        let eq = abs(abs(abs(app(Expr::Var(0), Expr::Var(1)))));
        let x_eq_foo = app(app(eq, Expr::Str("x")), Expr::Str("foo"));
        let let_y_x = app(
            app(
                Expr::Var(3), // let macro
                app(Expr::Str("Binding"), Expr::Str("y")),
            ),
            app(Expr::Str("Value"), Expr::Var(0)), // var x
        );
        let f_y = app(Expr::Var(3), Expr::Var(0));
        let expected = abs(app(x_eq_foo, abs(app(let_y_x, abs(f_y)))));

        let mut ctx = Ctx::default();
        ctx.vars.push("let");
        ctx.vars.push("f");

        let result = desugar(ast, &mut ctx).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn let_var_in_outer() {
        // { :x = "foo", let(:y, x), f(y) }

        let x_eq_foo = Ast::Call(Ast::Var("=").into(), vec![Ast::Binding("x"), Ast::Str("foo")]);
        let let_y_x = Ast::Call(Ast::Var("let").into(), vec![Ast::Binding("y"), Ast::Var("x")]);
        let f_y = Ast::Call(Ast::Var("f").into(), vec![Ast::Var("y")]);

        let ast = Ast::Block(vec![x_eq_foo, let_y_x, f_y]);

        let eq = abs(abs(abs(app(Expr::Var(0), Expr::Var(1)))));
        let x_eq_foo = app(app(eq, Expr::Str("x")), Expr::Str("foo"));
        let let_y_x = app(
            app(
                Expr::Var(3), // let macro
                app(Expr::Str("Binding"), Expr::Str("y")),
            ),
            app(Expr::Str("Value"), Expr::Var(0)), // var x
        );
        let f_y = app(Expr::Var(3), Expr::Var(0));
        let expected = abs(app(x_eq_foo, abs(app(let_y_x, abs(f_y)))));

        let mut ctx = Ctx::default();
        ctx.vars.push("let");
        ctx.vars.push("f");

        let result = desugar(ast, &mut ctx).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn let_var_in_outer_then_side_effects() {
        // { :x = "foo", let(:y, x), f(y), g(x) }

        let x_eq_foo = Ast::Call(Ast::Var("=").into(), vec![Ast::Binding("x"), Ast::Str("foo")]);
        let let_y_x = Ast::Call(Ast::Var("let").into(), vec![Ast::Binding("y"), Ast::Var("x")]);
        let f_y = Ast::Call(Ast::Var("f").into(), vec![Ast::Var("y")]);
        let g_x = Ast::Call(Ast::Var("g").into(), vec![Ast::Var("x")]);

        let ast = Ast::Block(vec![x_eq_foo, let_y_x, f_y, g_x]);

        let eq = abs(abs(abs(app(Expr::Var(0), Expr::Var(1)))));
        let x_eq_foo = app(app(eq, Expr::Str("x")), Expr::Str("foo"));
        let let_y_x = app(
            app(
                Expr::Var(4), // let macro
                app(Expr::Str("Binding"), Expr::Str("y")),
            ),
            app(Expr::Str("Value"), Expr::Var(0)), // var x
        );
        let f_y = app(Expr::Var(4), Expr::Var(0));
        let g_x = app(Expr::Var(4), Expr::Var(2));

        // y => (_ => g(x))(f(y))
        let f_y_then_g_x = abs(app(abs(g_x), f_y));
        let expected = abs(app(x_eq_foo, abs(app(let_y_x, f_y_then_g_x))));

        let mut ctx = Ctx::default();
        ctx.vars.push("let");
        ctx.vars.push("f");
        ctx.vars.push("g");

        let result = desugar(ast, &mut ctx).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn recursive_fn() {
        // { def(:f(x), { f(x) }), f("foo") }

        let f_x_signature = Ast::Call(Ast::Binding("f").into(), vec![Ast::Var("x")]);
        let f_x_body =
            Ast::Block(vec![Ast::Call(Ast::Var("f").into(), vec![Ast::Var("x").into()])]);
        let def_f_x = Ast::Call(Ast::Var("def").into(), vec![f_x_signature, f_x_body]);
        let f_foo = Ast::Call(Ast::Var("f").into(), vec![Ast::Str("foo")]);

        let ast = Ast::Block(vec![def_f_x, f_foo]);

        let def = Expr::Var(1);
        let f_args = app(Expr::Str("Nil"), app(Expr::Str("Binding"), Expr::Str("x")));
        let f_x_signature =
            app(app(Expr::Str("Call"), app(Expr::Str("Binding"), Expr::Str("f"))), f_args);
        let f_x_body = abs(abs(app(Expr::Var(1), Expr::Var(0))));
        let f_foo = app(Expr::Var(0), Expr::Str("foo"));
        let expected = abs(app(app(app(def, f_x_signature), f_x_body), abs(f_foo)));

        let mut ctx = Ctx::default();
        ctx.vars.push("def");
        assert_eq!(desugar(ast, &mut ctx).unwrap(), expected);
    }
}
