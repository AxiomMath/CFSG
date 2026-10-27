module

public import Certificates.Kernel.HS589207.D
public import Certificates.Kernel.Misc.Perm.HS100.Base
public import Certificates.Data.Kernel.DcHSOutK
public import Certificates.Data.Kernel.DcK
public import Certificates.Data.DcHSOut

public section

namespace CFSG.KD.HS589207

open CFSG.KC.DcHSOutK CFSG.KC.Enum

@[expose] noncomputable def h7 (X q : Nat) : Nat := pg 7 (CFSG.KS.mask 7) X q

@[expose] noncomputable def A (l q : Nat) : Nat :=
  if l = 0 then h7 (CertificateChecks.KernelMisc.HS100.HX.F 0) q
  else if l = 1 then h7 (CertificateChecks.KernelMisc.HS100.HX.F 1) q
  else if l = 2 then fl (TB.TF 0) q else fl (TB.TF 1) q

@[expose] noncomputable def uF (q : Nat) : Nat := h7 (CertificateChecks.KernelMisc.HS100.HX.F 15) q

@[expose] noncomputable def GM (t q : Nat) : Nat := fl (TB.TF (15 + t)) q

@[expose] noncomputable def EM : CFSG.KC.DcK.EnumK := CFSG.KC.DcK.recK 11520 100 MR.TF

@[expose] noncomputable def mF (k q : Nat) : Nat := fl (MR.TF k) q

@[expose] noncomputable def wF (q : Nat) : Nat := fl (TB.TF 2) q

@[expose] noncomputable def r0F (q : Nat) : Nat := fl (TB.TF 3) q

@[expose] noncomputable def gF (q : Nat) : Nat := fl (TB.TF 4) q

@[expose] noncomputable def invG (j q : Nat) : Nat := fl (TB.TF (5 + j)) q

@[expose] noncomputable def FP (i : Nat) : Nat := fl (FR.TF i) 8

@[expose] noncomputable def FL (i : Nat) : Nat := fl (FR.TF i) 9

@[expose] noncomputable def FPOS (e : Nat) : Nat := fl (FR.TF (e / 4)) (10 + e % 4)

@[expose] noncomputable def Fsig (i : Nat) : Nat := fl (FR.TF i) 14

@[expose] noncomputable def Fsinv (i : Nat) : Nat := fl (FR.TF i) 15

@[expose] noncomputable def CP (i : Nat) : Nat := fl (CR.TF i) 100

@[expose] noncomputable def CL (i : Nat) : Nat := fl (CR.TF i) 101

@[expose] noncomputable def CPOS (e : Nat) : Nat :=
  fl (CR.TF (e / 4)) (102 + e % 4)

@[expose] noncomputable def Csig (i : Nat) : Nat := fl (CR.TF i) 106

@[expose] noncomputable def Csinv (i : Nat) : Nat := fl (CR.TF i) 107

@[expose] noncomputable def I0 : List Nat := (List.range 16).map (fl (IX.TF 0))

@[expose] noncomputable def IO : List Nat := (List.range 16).map (fl (IX.TF 1))

@[expose] noncomputable def IG : List Nat := (List.range 10).map (fl (IX.TF 2))

@[expose] noncomputable def cF (j q : Nat) : Nat :=
  mF (CFSG.Quasithin.H13.LocDbl.HSLoc.goodIdx.getD j 0) (r0F (invG j q))

@[expose] noncomputable def mx (i : Nat) : Nat → Nat :=
  CFSG.KC.E64F.wordF A (CFSG.Quasithin.H13.LocDbl.HSLoc.mooreWords.getD (i - 1) [])

@[expose] noncomputable def mooreK : Bool :=
  decide (CFSG.Quasithin.H13.LocDbl.HSLoc.mooreWords.length = 6) &&
  eqF (fun q => mx 1 (mx 1 (mx 1 q))) (fun q => q) && !eqF (mx 1) (fun q => q) &&
    (List.range' 2 5).all (fun j => eqF (fun q => mx j (mx j q)) (fun q => q) &&
      eqF (fun q => mx (j - 1) (mx j (mx (j - 1) (mx j (mx (j - 1) (mx j q)))))) (fun q => q)) &&
    (List.range' 1 4).all (fun i => (List.range' (i + 2) (5 - i)).all fun j =>
      eqF (fun q => mx i (mx j (mx i (mx j q)))) (fun q => q)) &&
    CFSG.Quasithin.H13.LocDbl.HSLoc.mooreWords.all (fun w => commF (CFSG.KC.E64F.wordF A w) r0F)

end CFSG.KD.HS589207

end
