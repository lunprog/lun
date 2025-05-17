use lun_diag::{DiagnosticSink, StageResult};
use lun_semack::ckast::CkChunk;

#[derive(Debug, Clone)]
pub struct CodeGenerator {
    ast: CkChunk,
    sink: DiagnosticSink,
}

impl CodeGenerator {
    pub const fn new(ast: CkChunk, sink: DiagnosticSink) -> CodeGenerator {
        CodeGenerator { ast, sink }
    }

    pub fn produce(&mut self) -> StageResult<()> {
        StageResult::Good(())
    }
}
