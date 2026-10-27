module

public import Certificates.Kernel.PropA.Data
public import Certificates.Kernel.PropA.Words
public import Certificates.Data.Kernel.Spor.PRec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PRec

theorem pa450010_perm1 :
    allN 4 (fun j => permOK 28 5 (mask 5) (28 * 5) (pa450010S1 j) (pa450010S1I j)) = true := by
  quickRfl

theorem pa450010_perm2 :
    allN 4 (fun j => permOK 28 5 (mask 5) (28 * 5) (pa450010S2 j) (pa450010S2I j)) = true := by
  quickRfl

theorem pa450010_XD_root :
    wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 2 pa450010wx pa450010XD.R = true := by
  quickRfl
theorem pa450010_XD_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010XD.R 396 pa450010XD.k
    pa450010XD.G pa450010XD.GI pa450010XD.cnt pa450010XD.T pa450010XD.PL 2 pa450010S1 pa450010S1I
    pa450010wD = true := by quickRfl
theorem pa450010_XD_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010XD.G pa450010XD.GI
    pa450010XD.k pa450010XD.cnt pa450010XD.T pa450010XD.PL pa450010XD.POS pa450010XD.SRT
    pa450010XD.SRI 0 396 = true := by quickRfl

theorem pa450010_AD_root :
    wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 2 [1] pa450010AD.R = true := by
  quickRfl
theorem pa450010_AD_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010AD.R 495 pa450010AD.k
    pa450010AD.G pa450010AD.GI pa450010AD.cnt pa450010AD.T pa450010AD.PL 2 pa450010S1 pa450010S1I
    pa450010wD = true := by quickRfl
theorem pa450010_AD_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010AD.G pa450010AD.GI
    pa450010AD.k pa450010AD.cnt pa450010AD.T pa450010AD.PL pa450010AD.POS pa450010AD.SRT
    pa450010AD.SRI 0 495 = true := by quickRfl

theorem pa450010_UD_root :
    wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 2 pa450010wu pa450010UD.R = true := by
  quickRfl
theorem pa450010_UD_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010UD.R 2640
    pa450010UD.k pa450010UD.G pa450010UD.GI pa450010UD.cnt pa450010UD.T pa450010UD.PL 2 pa450010S1
    pa450010S1I pa450010wD = true := by quickRfl
theorem pa450010_UD_sl0 : penumSlK 28 5 (mask 5) (28 * 5) true pa450010UD.G pa450010UD.GI
    pa450010UD.k pa450010UD.cnt pa450010UD.T pa450010UD.PL pa450010UD.POS pa450010UD.SRT
    pa450010UD.SRI 0 1000 = true := by quickRfl
theorem pa450010_UD_sl1 : penumSlK 28 5 (mask 5) (28 * 5) true pa450010UD.G pa450010UD.GI
    pa450010UD.k pa450010UD.cnt pa450010UD.T pa450010UD.PL pa450010UD.POS pa450010UD.SRT
    pa450010UD.SRI 1000 1000 = true := by quickRfl
theorem pa450010_UD_sl2 : penumSlK 28 5 (mask 5) (28 * 5) true pa450010UD.G pa450010UD.GI
    pa450010UD.k pa450010UD.cnt pa450010UD.T pa450010UD.PL pa450010UD.POS pa450010UD.SRT
    pa450010UD.SRI 2000 640 = true := by quickRfl

theorem pa450010_C10_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 4
    (pa450010wReps.getD 0 []) pa450010C10.R = true := by quickRfl
theorem pa450010_C10_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C10.R 495
    pa450010C10.k pa450010C10.G pa450010C10.GI pa450010C10.cnt pa450010C10.T pa450010C10.PL 4
    pa450010S1 pa450010S1I pa450010wK = true := by quickRfl
theorem pa450010_C10_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C10.G pa450010C10.GI
    pa450010C10.k pa450010C10.cnt pa450010C10.T pa450010C10.PL pa450010C10.POS pa450010C10.SRT
    pa450010C10.SRI 0 495 = true := by quickRfl

theorem pa450010_C11_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 4
    (pa450010wReps.getD 1 []) pa450010C11.R = true := by quickRfl
theorem pa450010_C11_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C11.R 495
    pa450010C11.k pa450010C11.G pa450010C11.GI pa450010C11.cnt pa450010C11.T pa450010C11.PL 4
    pa450010S1 pa450010S1I pa450010wK = true := by quickRfl
theorem pa450010_C11_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C11.G pa450010C11.GI
    pa450010C11.k pa450010C11.cnt pa450010C11.T pa450010C11.PL pa450010C11.POS pa450010C11.SRT
    pa450010C11.SRI 0 495 = true := by quickRfl

theorem pa450010_C12_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 4
    (pa450010wReps.getD 2 []) pa450010C12.R = true := by quickRfl
theorem pa450010_C12_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C12.R 396
    pa450010C12.k pa450010C12.G pa450010C12.GI pa450010C12.cnt pa450010C12.T pa450010C12.PL 4
    pa450010S1 pa450010S1I pa450010wK = true := by quickRfl
theorem pa450010_C12_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C12.G pa450010C12.GI
    pa450010C12.k pa450010C12.cnt pa450010C12.T pa450010C12.PL pa450010C12.POS pa450010C12.SRT
    pa450010C12.SRI 0 396 = true := by quickRfl

theorem pa450010_C13_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 4
    (pa450010wReps.getD 3 []) pa450010C13.R = true := by quickRfl
theorem pa450010_C13_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C13.R 396
    pa450010C13.k pa450010C13.G pa450010C13.GI pa450010C13.cnt pa450010C13.T pa450010C13.PL 4
    pa450010S1 pa450010S1I pa450010wK = true := by quickRfl
theorem pa450010_C13_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C13.G pa450010C13.GI
    pa450010C13.k pa450010C13.cnt pa450010C13.T pa450010C13.PL pa450010C13.POS pa450010C13.SRT
    pa450010C13.SRI 0 396 = true := by quickRfl

theorem pa450010_C14_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 4
    (pa450010wReps.getD 4 []) pa450010C14.R = true := by quickRfl
theorem pa450010_C14_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C14.R 792
    pa450010C14.k pa450010C14.G pa450010C14.GI pa450010C14.cnt pa450010C14.T pa450010C14.PL 4
    pa450010S1 pa450010S1I pa450010wK = true := by quickRfl
theorem pa450010_C14_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C14.G pa450010C14.GI
    pa450010C14.k pa450010C14.cnt pa450010C14.T pa450010C14.PL pa450010C14.POS pa450010C14.SRT
    pa450010C14.SRI 0 792 = true := by quickRfl

theorem pa450010_C15_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 4
    (pa450010wReps.getD 5 []) pa450010C15.R = true := by quickRfl
theorem pa450010_C15_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C15.R 792
    pa450010C15.k pa450010C15.G pa450010C15.GI pa450010C15.cnt pa450010C15.T pa450010C15.PL 4
    pa450010S1 pa450010S1I pa450010wK = true := by quickRfl
theorem pa450010_C15_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C15.G pa450010C15.GI
    pa450010C15.k pa450010C15.cnt pa450010C15.T pa450010C15.PL pa450010C15.POS pa450010C15.SRT
    pa450010C15.SRI 0 792 = true := by quickRfl

theorem pa450010_C20_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S2 pa450010S2I 4
    (pa450010wReps.getD 0 []) pa450010C20.R = true := by quickRfl
theorem pa450010_C20_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C20.R 495
    pa450010C20.k pa450010C20.G pa450010C20.GI pa450010C20.cnt pa450010C20.T pa450010C20.PL 4
    pa450010S2 pa450010S2I pa450010wK = true := by quickRfl
theorem pa450010_C20_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C20.G pa450010C20.GI
    pa450010C20.k pa450010C20.cnt pa450010C20.T pa450010C20.PL pa450010C20.POS pa450010C20.SRT
    pa450010C20.SRI 0 495 = true := by quickRfl

theorem pa450010_C21_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S2 pa450010S2I 4
    (pa450010wReps.getD 1 []) pa450010C21.R = true := by quickRfl
theorem pa450010_C21_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C21.R 495
    pa450010C21.k pa450010C21.G pa450010C21.GI pa450010C21.cnt pa450010C21.T pa450010C21.PL 4
    pa450010S2 pa450010S2I pa450010wK = true := by quickRfl
theorem pa450010_C21_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C21.G pa450010C21.GI
    pa450010C21.k pa450010C21.cnt pa450010C21.T pa450010C21.PL pa450010C21.POS pa450010C21.SRT
    pa450010C21.SRI 0 495 = true := by quickRfl

theorem pa450010_C22_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S2 pa450010S2I 4
    (pa450010wReps.getD 2 []) pa450010C22.R = true := by quickRfl
theorem pa450010_C22_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C22.R 396
    pa450010C22.k pa450010C22.G pa450010C22.GI pa450010C22.cnt pa450010C22.T pa450010C22.PL 4
    pa450010S2 pa450010S2I pa450010wK = true := by quickRfl
theorem pa450010_C22_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C22.G pa450010C22.GI
    pa450010C22.k pa450010C22.cnt pa450010C22.T pa450010C22.PL pa450010C22.POS pa450010C22.SRT
    pa450010C22.SRI 0 396 = true := by quickRfl

theorem pa450010_C23_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S2 pa450010S2I 4
    (pa450010wReps.getD 3 []) pa450010C23.R = true := by quickRfl
theorem pa450010_C23_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C23.R 396
    pa450010C23.k pa450010C23.G pa450010C23.GI pa450010C23.cnt pa450010C23.T pa450010C23.PL 4
    pa450010S2 pa450010S2I pa450010wK = true := by quickRfl
theorem pa450010_C23_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C23.G pa450010C23.GI
    pa450010C23.k pa450010C23.cnt pa450010C23.T pa450010C23.PL pa450010C23.POS pa450010C23.SRT
    pa450010C23.SRI 0 396 = true := by quickRfl

theorem pa450010_C24_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S2 pa450010S2I 4
    (pa450010wReps.getD 4 []) pa450010C24.R = true := by quickRfl
theorem pa450010_C24_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C24.R 792
    pa450010C24.k pa450010C24.G pa450010C24.GI pa450010C24.cnt pa450010C24.T pa450010C24.PL 4
    pa450010S2 pa450010S2I pa450010wK = true := by quickRfl
theorem pa450010_C24_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C24.G pa450010C24.GI
    pa450010C24.k pa450010C24.cnt pa450010C24.T pa450010C24.PL pa450010C24.POS pa450010C24.SRT
    pa450010C24.SRI 0 792 = true := by quickRfl

theorem pa450010_C25_root : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S2 pa450010S2I 4
    (pa450010wReps.getD 5 []) pa450010C25.R = true := by quickRfl
theorem pa450010_C25_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010C25.R 792
    pa450010C25.k pa450010C25.G pa450010C25.GI pa450010C25.cnt pa450010C25.T pa450010C25.PL 4
    pa450010S2 pa450010S2I pa450010wK = true := by quickRfl
theorem pa450010_C25_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010C25.G pa450010C25.GI
    pa450010C25.k pa450010C25.cnt pa450010C25.T pa450010C25.PL pa450010C25.POS pa450010C25.SRT
    pa450010C25.SRI 0 792 = true := by quickRfl

end CertificateChecks.KernelPropA

end
