module

public import Certificates.Data.Kernel.F4T
public import Certificates.Kernel.Huppert.C188003Data

public section

set_option maxRecDepth 100000

namespace CFSG.KD.C188003

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.F4T

theorem c188003_wit0 : witOK rowCodes (chunkT 30 0 invsT) (chunkT 30 0 wits) = true := by
  decide +kernel

theorem c188003_wit1 : witOK rowCodes (chunkT 30 1 invsT) (chunkT 30 1 wits) = true := by
  decide +kernel

theorem c188003_wit2 : witOK rowCodes (chunkT 30 2 invsT) (chunkT 30 2 wits) = true := by
  decide +kernel

theorem c188003_wit3 : witOK rowCodes (chunkT 30 3 invsT) (chunkT 30 3 wits) = true := by
  decide +kernel

theorem c188003_wit4 : witOK rowCodes (chunkT 30 4 invsT) (chunkT 30 4 wits) = true := by
  decide +kernel

theorem c188003_wit5 : witOK rowCodes (chunkT 30 5 invsT) (chunkT 30 5 wits) = true := by
  decide +kernel

theorem c188003_wit6 : witOK rowCodes (chunkT 30 6 invsT) (chunkT 30 6 wits) = true := by
  decide +kernel

theorem c188003_wit7 : witOK rowCodes (chunkT 30 7 invsT) (chunkT 30 7 wits) = true := by
  decide +kernel

theorem c188003_wit8 : witOK rowCodes (chunkT 30 8 invsT) (chunkT 30 8 wits) = true := by
  decide +kernel

theorem c188003_wit9 : witOK rowCodes (chunkT 30 9 invsT) (chunkT 30 9 wits) = true := by
  decide +kernel

theorem c188003_wit10 : witOK rowCodes (chunkT 30 10 invsT) (chunkT 30 10 wits) = true := by
  decide +kernel

theorem c188003_wit_len : Nat.beq invsT.length 315 && Nat.beq wits.length 315 = true := by
  decide +kernel

theorem c188003_rows0 : t3RowsOK (chunkT 24 0 rowCodes) (chunkT 24 0 rowW1) (chunkT 24 0 rowWO)
    (chunkT 24 0 rowWO2) = true := by
  decide +kernel

theorem c188003_rows1 : t3RowsOK (chunkT 24 1 rowCodes) (chunkT 24 1 rowW1) (chunkT 24 1 rowWO)
    (chunkT 24 1 rowWO2) = true := by
  decide +kernel

theorem c188003_rows2 : t3RowsOK (chunkT 24 2 rowCodes) (chunkT 24 2 rowW1) (chunkT 24 2 rowWO)
    (chunkT 24 2 rowWO2) = true := by
  decide +kernel

theorem c188003_rows_len : Nat.beq rowCodes.length 72 && Nat.beq rowW1.length 72 &&
    Nat.beq rowWO.length 72 && Nat.beq rowWO2.length 72 = true := by
  decide +kernel

theorem c188003_nonroot : nonRootsOK omega gks rowCodes rowIdx rowG = true := by
  decide +kernel

theorem c188003_chain : Nat.beq omega.length 6 && Nat.beq gks.length 6 &&
    Nat.beq chainW.length 6 && ((omega.zip (gks.zip chainW)).all fun p =>
      chainOK p.1 (p.2.1.getD 0 []) (p.2.1.getD 1 []) p.2.2) = true := by
  decide +kernel

theorem c188003_close0 : closeOK (omega.getD 0 []) (t4Reps.getD 0 []) (t4Masks.getD 0 []) = true := by
  decide +kernel

theorem c188003_close1 : closeOK (omega.getD 1 []) (t4Reps.getD 1 []) (t4Masks.getD 1 []) = true := by
  decide +kernel

theorem c188003_close2 : closeOK (omega.getD 2 []) (t4Reps.getD 2 []) (t4Masks.getD 2 []) = true := by
  decide +kernel

theorem c188003_close3 : closeOK (omega.getD 3 []) (t4Reps.getD 3 []) (t4Masks.getD 3 []) = true := by
  decide +kernel

theorem c188003_close4 : closeOK (omega.getD 4 []) (t4Reps.getD 4 []) (t4Masks.getD 4 []) = true := by
  decide +kernel

theorem c188003_close5 : closeOK (omega.getD 5 []) (t4Reps.getD 5 []) (t4Masks.getD 5 []) = true := by
  decide +kernel

@[expose] noncomputable def t4wAt (i c : Nat) : Bool :=
  t4WordsOK (omega.getD i []) (t4R.getD i []) (chunkT 28 c (t4Reps.getD i []).tail)
    (chunkT 28 c (t4Words.getD i []))

theorem c188003_t4w00 : t4wAt 0 0 = true := by decide +kernel
theorem c188003_t4w01 : t4wAt 0 1 = true := by decide +kernel
theorem c188003_t4w10 : t4wAt 1 0 = true := by decide +kernel
theorem c188003_t4w11 : t4wAt 1 1 = true := by decide +kernel
theorem c188003_t4w20 : t4wAt 2 0 = true := by decide +kernel
theorem c188003_t4w21 : t4wAt 2 1 = true := by decide +kernel
theorem c188003_t4w30 : t4wAt 3 0 = true := by decide +kernel
theorem c188003_t4w31 : t4wAt 3 1 = true := by decide +kernel
theorem c188003_t4w40 : t4wAt 4 0 = true := by decide +kernel
theorem c188003_t4w41 : t4wAt 4 1 = true := by decide +kernel
theorem c188003_t4w50 : t4wAt 5 0 = true := by decide +kernel
theorem c188003_t4w51 : t4wAt 5 1 = true := by decide +kernel

end CFSG.KD.C188003
