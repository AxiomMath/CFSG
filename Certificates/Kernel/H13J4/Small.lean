
module

public import CFSG.Quasithin.H13.J4ClassCheckInputs

public section

namespace CertificateChecks.KernelH13.J4Small

open CFSG.Quasithin.H13.J4
open CFSG.Sporadic.J4Schreier (xColumns yColumns xInvColumns yInvColumns app11)
open CFSG.Quasithin.H13.J4.Native (imCols colsBounded)

theorem im2 : imOK m2Cols (imCols m2Cols) = true ∧ (imCols m2Cols).length = 16 := by
  decide +kernel

theorem im3 : imOK xColumns (imCols xColumns) = true ∧ (imCols xColumns).length = 32 := by
  decide +kernel

theorem ker3 : app11 xColumns 1096 = 1096 ∧ 1096 ∉ imCols xColumns ∧
    ∀ a < 2048, app11 xColumns a = a → a ∈ imCols xColumns ∨ (a ^^^ 1096) ∈ imCols xColumns := by
  decide +kernel

theorem bounded : colsBounded xColumns = true ∧ colsBounded xInvColumns = true ∧
    colsBounded yColumns = true ∧ colsBounded yInvColumns = true ∧ colsBounded m2Cols = true := by
  decide +kernel

end CertificateChecks.KernelH13.J4Small

end
