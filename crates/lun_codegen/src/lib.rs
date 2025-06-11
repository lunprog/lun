use lun_bc::{
    BcBlob,
    bin::{LBType, LunBin, LunBinBuilder},
};
use lun_diag::{Diagnostic, DiagnosticSink, StageResult};
use lun_semack::ckast::{BinOp, CkChunk, CkExpr, CkExpression, CkStmt, UnaryOp};

#[derive(Debug, Clone)]
pub struct CodeGenerator {
    ast: CkChunk,
    sink: DiagnosticSink,
    typ: LBType,
    bc: BcBlob,
}

impl CodeGenerator {
    pub fn new(ast: CkChunk, sink: DiagnosticSink, typ: LBType) -> CodeGenerator {
        CodeGenerator {
            ast,
            sink,
            typ,
            bc: BcBlob::new(),
        }
    }

    pub fn produce(&mut self) -> StageResult<LunBin> {
        let mut builder = LunBinBuilder::new();
        builder.typ(self.typ);
        // TODO: make a simpler IR

        let CkStmt::Assignement {
            variable: _,
            ref value,
        } = self.ast.stmts[0].stmt
        else {
            todo!();
        };

        self.gen_expr(value.clone()).unwrap();

        builder.section(LunBin::SECTION_CODE, self.bc.code_data());

        if self.sink.failed() {
            return StageResult::Fail(self.sink.clone());
        }
        StageResult::Good(builder.build().unwrap())
    }

    pub fn gen_expr(&mut self, expr: CkExpression) -> Result<(), Diagnostic> {
        match expr.expr {
            CkExpr::IntLit(_) => {
                todo!()
            }
            CkExpr::BoolLit(_) => {
                // TODO: make only two, constants true and false, no need to
                // create new ones each time, or create a new opcode
                todo!("bool literal compilation")
            }
            CkExpr::StringLit(_) => {
                todo!("string literal compilation")
            }
            CkExpr::Grouping(expr) => {
                self.gen_expr(*expr)?;
            }
            CkExpr::Ident(_) => todo!("ident expr"),
            CkExpr::Binary { lhs, op, rhs } => {
                self.gen_expr(*lhs)?;
                self.gen_expr(*rhs)?;

                match op {
                    BinOp::Add => self.bc.write_add(),
                    BinOp::Sub => self.bc.write_sub(),
                    BinOp::Mul => self.bc.write_mul(),
                    BinOp::Div => self.bc.write_div(),
                    _ => todo!("implement comparaison operators"),
                }
            }
            CkExpr::Unary { op, expr } => {
                self.gen_expr(*expr)?;

                match op {
                    UnaryOp::Negation => self.bc.write_neg(),
                    UnaryOp::Not => todo!("not operator compilation"),
                }
            }
            _ => todo!("other expression to compile"),
        }
        Ok(())
    }
}
