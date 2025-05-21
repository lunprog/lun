use lun_bc::bin::{LBType, LunBinBuilder};
use lun_diag::{DiagnosticSink, StageResult};
use lun_semack::ckast::CkChunk;

#[derive(Debug, Clone)]
pub struct CodeGenerator {
    ast: CkChunk,
    sink: DiagnosticSink,
    typ: LBType,
}

impl CodeGenerator {
    pub const fn new(ast: CkChunk, sink: DiagnosticSink, typ: LBType) -> CodeGenerator {
        CodeGenerator { ast, sink, typ }
    }

    pub fn produce(&mut self) -> StageResult<()> {
        let mut builder = LunBinBuilder::new();
        builder.typ(self.typ);

        StageResult::Good(())
    }
}
