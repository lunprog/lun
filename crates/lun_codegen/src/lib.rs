use lun_bc::{
    BcBlob,
    bin::{LBType, LunBin, LunBinBuilder},
};
use lun_diag::{DiagnosticSink, StageResult};
use lun_semack::ckast::CkChunk;

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
        todo!("REMAKE THE CODEGEN");

        #[allow(unreachable_code)]
        let _ = &self.ast; // REMOVE ME AFTER

        let mut builder = LunBinBuilder::new();
        builder.typ(self.typ);

        builder.section(LunBin::SECTION_CODE, self.bc.code_data());

        if self.sink.failed() {
            return StageResult::Fail(self.sink.clone());
        }
        StageResult::Good(builder.build().unwrap())
    }
}
