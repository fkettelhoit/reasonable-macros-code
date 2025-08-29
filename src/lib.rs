use std::{cmp::max, mem};

#[derive(Debug, Clone)]
pub enum Ast {
    Var(&'static str),
    Str(&'static str),
    Binding(usize, &'static str),
    Macro(usize, &'static str),
    Block(Vec<Ast>),
    Call(Box<Ast>, Vec<Ast>),
}

#[derive(Debug, Clone, Default)]
pub struct Ctx {
    pub bindings: Vec<(usize, bool, &'static str)>, // bool: true for macro, false for binding
    pub vars: Vec<(bool, &'static str)>,
}

impl Ctx {
    pub fn drain_bindings(&mut self) -> Vec<(bool, &'static str)> {
        let mut kept = vec![];
        let mut drained = vec![];
        for (lvl, is_macro, name) in self.bindings.drain(..) {
            if lvl > 0 {
                kept.push((lvl, is_macro, name));
            }
            drained.push((is_macro, name));
        }
        self.bindings = kept;
        drained
    }

    pub fn clear_bindings(&mut self) {
        self.bindings = self
            .bindings
            .drain(..)
            .filter(|(lvl, _, _)| *lvl > 0)
            .map(|(lvl, is_macro, name)| (lvl - 1, is_macro, name))
            .collect()
    }
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
    ctx.vars.iter().rev().position(|(_, x)| *x == v)
}

fn is_macro(ast: &Ast, ctx: &Ctx) -> bool {
    if let Ast::Var(v) = ast {
        if let Some((true, _)) = ctx.vars.iter().rev().find(|(_, x)| x == v) {
            return true;
        }
    }
    false
}

fn has_bindings(ast: &Ast, ctx: &Ctx) -> bool {
    match ast {
        Ast::Binding(_, _) | Ast::Macro(_, _) => true,
        Ast::Var(_) | Ast::Str(_) | Ast::Block(_) => false,
        Ast::Call(f, _) if is_macro(f, ctx) => false,
        Ast::Call(f, _) if has_bindings(f, ctx) => true,
        Ast::Call(_, args) => args.iter().any(|arg| has_bindings(arg, ctx)),
    }
}

fn desugar_macro(ast: Ast, ctx: &mut Ctx) -> Result<Expr, &'static str> {
    fn desug_all(xs: Vec<Ast>, ctx: &mut Ctx) -> Result<Vec<Expr>, &'static str> {
        xs.into_iter().map(|x| desugar_macro(x, ctx)).collect()
    }
    match ast {
        Ast::Call(f, args) if has_bindings(&ast, ctx) => {
            let f = desugar_macro(*f, ctx)?;
            let args = desug_all(args, ctx)?;
            let list = args.into_iter().fold(Expr::Str("Nil"), |l, x| app(l, x));
            Ok(app(app(Expr::Str("Call"), f), list))
        }
        Ast::Var(_) | Ast::Str(_) | Ast::Call(_, _) => {
            Ok(app(Expr::Str("Value"), desugar(ast, ctx)?))
        }
        Ast::Binding(_, _) | Ast::Macro(_, _) => Ok(app(Expr::Str("Binding"), desugar(ast, ctx)?)),
        Ast::Block(_) => desugar(ast, ctx),
    }
}

pub fn desugar(ast: Ast, ctx: &mut Ctx) -> Result<Expr, &'static str> {
    match ast {
        Ast::Var(v) => match resolve_var(&v, ctx) {
            Some(v) => Ok(Expr::Var(v)),
            None => match v {
                "=" => Ok(abs(abs(abs(app(Expr::Var(0), Expr::Var(1)))))),
                "=>" => Ok(abs(abs(Expr::Var(0)))),
                _ => Err(v),
            },
        },
        Ast::Str(s) => Ok(Expr::Str(s)),
        Ast::Binding(lvl, name) => {
            ctx.bindings.push((lvl, false, name));
            Ok(Expr::Str(name))
        }
        Ast::Macro(lvl, name) => {
            ctx.bindings.push((lvl, true, name));
            Ok(Expr::Str(name))
        }
        Ast::Block(mut items) => {
            let mut desugared = vec![];
            if items.is_empty() {
                items.push(Ast::Str("Nil"));
            }
            for ast in items {
                let bindings = ctx.bindings.len();
                let drained = ctx.drain_bindings();
                ctx.vars.extend(drained);
                if bindings == 0 {
                    ctx.vars.push((false, ""))
                }
                desugared.push((bindings, desugar(ast, ctx)?));
            }
            let (mut bindings, mut expr) = desugared.pop().unwrap();
            expr = (0..max(1, bindings)).fold(expr, |x, _| abs(x));
            for (prev_bindings, x) in desugared.into_iter().rev() {
                let (f, arg) = if bindings == 0 { (expr, x) } else { (x, expr) };
                expr = (0..max(1, prev_bindings)).fold(app(f, arg), |x, _| abs(x));
                ctx.vars.truncate(ctx.vars.len() - max(1, bindings));
                bindings = prev_bindings;
            }
            ctx.vars.truncate(ctx.vars.len() - max(1, bindings));
            ctx.clear_bindings();
            Ok(expr)
        }
        Ast::Call(f, args) => {
            let bindings = mem::replace(&mut ctx.bindings, vec![]);
            let is_macro = is_macro(&f, ctx);
            let mut f = desugar(*f, ctx)?;
            if args.is_empty() {
                f = app(f, Expr::Str("Nil"));
            }
            for x in args {
                f = app(f, if is_macro { desugar_macro(x, ctx)? } else { desugar(x, ctx)? })
            }
            ctx.bindings.splice(0..0, bindings);
            Ok(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Ast, Ctx, Expr, abs, app, desugar};

    #[test]
    fn lambda_app() {
        // (:x => { f(x) })("foo")

        let block = Ast::Block(vec![Ast::Call(Ast::Var("f").into(), vec![Ast::Var("x")])]);
        let lambda = Ast::Call(Ast::Var("=>").into(), vec![Ast::Binding(0, "x"), block]);
        let foo = Ast::Str("foo");
        let ast = Ast::Call(lambda.into(), vec![foo]);

        let block = abs(app(Expr::Var(1), Expr::Var(0)));
        let fat_arrow = abs(abs(Expr::Var(0)));
        let lambda = app(app(fat_arrow, Expr::Str("x")), block);
        let expected = app(lambda, Expr::Str("foo"));

        let mut ctx = Ctx::default();
        ctx.vars.push((false, "f"));
        assert_eq!(desugar(ast, &mut ctx).unwrap(), expected);
    }

    #[test]
    fn let_var_in_inner() {
        // { :x = "foo", let(:y, x, { f(y) }) }
        let x_eq_foo = Ast::Call(Ast::Var("=").into(), vec![Ast::Binding(0, "x"), Ast::Str("foo")]);
        let f_y = Ast::Call(Ast::Var("f").into(), vec![Ast::Var("y")]);
        let let_y_x_block = Ast::Call(
            Ast::Var("let").into(),
            vec![Ast::Binding(0, "y"), Ast::Var("x"), Ast::Block(vec![f_y])],
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
        ctx.vars.push((true, "let")); // let is a macro
        ctx.vars.push((false, "f"));

        let result = desugar(ast, &mut ctx).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn let_var_in_outer() {
        // { :x = "foo", let(:y, x), f(y) }

        let x_eq_foo = Ast::Call(Ast::Var("=").into(), vec![Ast::Binding(0, "x"), Ast::Str("foo")]);
        let let_y_x = Ast::Call(Ast::Var("let").into(), vec![Ast::Binding(0, "y"), Ast::Var("x")]);
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
        ctx.vars.push((true, "let")); // let is a macro
        ctx.vars.push((false, "f"));

        let result = desugar(ast, &mut ctx).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn let_var_in_outer_then_side_effects() {
        // { :x = "foo", let(:y, x), f(y), g(x) }

        let x_eq_foo = Ast::Call(Ast::Var("=").into(), vec![Ast::Binding(0, "x"), Ast::Str("foo")]);
        let let_y_x = Ast::Call(Ast::Var("let").into(), vec![Ast::Binding(0, "y"), Ast::Var("x")]);
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
        ctx.vars.push((true, "let")); // let is a macro
        ctx.vars.push((false, "f"));
        ctx.vars.push((false, "g"));

        let result = desugar(ast, &mut ctx).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn recursive_fn() {
        // { ::f(:x) = { f(x) }, f("foo") }

        let f_x_signature = Ast::Call(Ast::Binding(1, "f").into(), vec![Ast::Binding(0, "x")]);
        let f_x_body =
            Ast::Block(vec![Ast::Call(Ast::Var("f").into(), vec![Ast::Var("x").into()])]);
        let rec_f_x = Ast::Call(Ast::Var("=").into(), vec![f_x_signature, f_x_body]);
        let f_foo = Ast::Call(Ast::Var("f").into(), vec![Ast::Str("foo")]);

        let ast = Ast::Block(vec![rec_f_x, f_foo]);

        let eq = abs(abs(abs(app(Expr::Var(0), Expr::Var(1)))));
        let f_x_signature = app(Expr::Str("f"), Expr::Str("x"));
        let f_x_body = abs(abs(app(Expr::Var(1), Expr::Var(0))));
        let f_foo = app(Expr::Var(0), Expr::Str("foo"));
        let expected = abs(app(app(app(eq, f_x_signature), f_x_body), abs(f_foo)));

        let mut ctx = Ctx::default();
        assert_eq!(desugar(ast, &mut ctx).unwrap(), expected);
    }
}
