module

public import Certificates.Data.Kernel.G2Three.Sec1T3
public import Certificates.Kernel.G2Three.Sec1T3Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

theorem s3_tab0 : tabK PT RT PA PB 0 16 = true := by quickRfl
theorem s3_tab1 : tabK PT RT PA PB 16 16 = true := by quickRfl
theorem s3_tab2 : tabK PT RT PA PB 32 16 = true := by quickRfl
theorem s3_tab3 : tabK PT RT PA PB 48 16 = true := by quickRfl
theorem s3_tab4 : tabK PT RT PA PB 64 16 = true := by quickRfl
theorem s3_tab5 : tabK PT RT PA PB 80 16 = true := by quickRfl
theorem s3_tab6 : tabK PT RT PA PB 96 16 = true := by quickRfl
theorem s3_tab7 : tabK PT RT PA PB 112 16 = true := by quickRfl

theorem s3_col0 : colK PT PC 0 32 = true := by quickRfl
theorem s3_col1 : colK PT PC 32 32 = true := by quickRfl
theorem s3_col2 : colK PT PC 64 32 = true := by quickRfl
theorem s3_col3 : colK PT PC 96 32 = true := by quickRfl

theorem s3_invSq : (invK PT IV && sqK PT SQ) = true := by quickRfl

theorem s3_base : (Nat.beq GM M128 && Nat.beq N 408 && Nat.beq (fld(LMP, 0, M128)) 1) = true := by
  quickRfl

theorem s3_ord : ordK LMP OR 0 408 = true := by quickRfl

theorem s3_lat0 : rowsOK PT PC IV SQ GM LMP LGN OR LO0 0 = true := by quickRfl
theorem s3_lat1 : rowsOK PT PC IV SQ GM LMP LGN OR LO1 51 = true := by quickRfl
theorem s3_lat2 : rowsOK PT PC IV SQ GM LMP LGN OR LO2 102 = true := by quickRfl
theorem s3_lat3 : rowsOK PT PC IV SQ GM LMP LGN OR LO3 153 = true := by quickRfl
theorem s3_lat4 : rowsOK PT PC IV SQ GM LMP LGN OR LO4 204 = true := by quickRfl
theorem s3_lat5 : rowsOK PT PC IV SQ GM LMP LGN OR LO5 255 = true := by quickRfl
theorem s3_lat6 : rowsOK PT PC IV SQ GM LMP LGN OR LO6 306 = true := by quickRfl
theorem s3_lat7 : rowsOK PT PC IV SQ GM LMP LGN OR LO7 357 = true := by quickRfl

theorem s3_idx : Nat.beq (Nat.lor (Nat.lor (Nat.lor (idxAll LO0) (idxAll LO1))
    (Nat.lor (idxAll LO2) (idxAll LO3))) (Nat.lor (Nat.lor (idxAll LO4) (idxAll LO5))
    (Nat.lor (idxAll LO6) (idxAll LO7)))) (Nat.sub (Nat.shiftLeft 1 408) 2) = true := by quickRfl

end CFSG.KD.G2Three.Sec1T3

end
