module

public import Certificates.Kernel.LocalComp.L34RDefs
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC.L34X CFSG.PSL3Four.Native
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def L34S.T (i : Nat) : Nat := at8 L34S.TP (nat_lit 252) i
@[expose] noncomputable def L34S.E (i : Nat) : Nat := at16 L34S.EP (nat_lit 54) i
@[expose] noncomputable def L34S.S (i : Nat) : Nat := at16 L34S.SP (nat_lit 18) i
@[expose] noncomputable def L34S.SI (i : Nat) : Nat := at16 L34S.SIP (nat_lit 18) i
@[expose] noncomputable def L34O0.E (i : Nat) : Nat := at16 L34O0.EP (nat_lit 66) i
@[expose] noncomputable def L34O0.S (i : Nat) : Nat := at16 L34O0.SP (nat_lit 18) i
@[expose] noncomputable def L34O0.SI (i : Nat) : Nat := at16 L34O0.SIP (nat_lit 18) i
@[expose] noncomputable def L34O1.E (i : Nat) : Nat := at16 L34O1.EP (nat_lit 66) i
@[expose] noncomputable def L34O1.S (i : Nat) : Nat := at16 L34O1.SP (nat_lit 18) i
@[expose] noncomputable def L34O1.SI (i : Nat) : Nat := at16 L34O1.SIP (nat_lit 18) i
@[expose] noncomputable def L34O2.E (i : Nat) : Nat := at16 L34O2.EP (nat_lit 66) i
@[expose] noncomputable def L34O2.S (i : Nat) : Nat := at16 L34O2.SP (nat_lit 18) i
@[expose] noncomputable def L34O2.SI (i : Nat) : Nat := at16 L34O2.SIP (nat_lit 18) i
@[expose] noncomputable def L34O3.E (i : Nat) : Nat := at16 L34O3.EP (nat_lit 66) i
@[expose] noncomputable def L34O3.S (i : Nat) : Nat := at16 L34O3.SP (nat_lit 18) i
@[expose] noncomputable def L34O3.SI (i : Nat) : Nat := at16 L34O3.SIP (nat_lit 18) i

@[expose] noncomputable def L34S.ps (s : Nat) : Bool :=
  pinSl 42 6 3 L34R.G L34S.T L34S.E L34S.C L34S.S L34S.SI 20160 1344 18 s

theorem kBindR : (Nat.beq gTabs.size 6 && allN 6 fun k => bindArrK gTabs[k]! 42 6 (L34R.G k)) =
    true := by quickRfl

theorem kBindS : (Nat.beq gensS.size 3 && allN 3 fun k => bindArrK gensS[k]! 42 6 (L34R.G k)) =
    true := by quickRfl

theorem kPermR : allN 6 (fun k => permOK 42 6 (mask 6) (42 * 6) (L34R.G k)
    (pinvS 42 6 (mask 6) (L34R.G k))) = true := by quickRfl

theorem kHeadR : headK 42 6 6 L34R.G L34R.T L34R.C 180 241920 (pidn 42 6) = true := by quickRfl

theorem kHeadS : headK 42 6 3 L34R.G L34S.T L34S.C 15 20160 (pidn 42 6) = true := by quickRfl

theorem kOrb0 : orbK 42 6 6 L34R.G GI (L34O.T 0) L34O0.E L34O0.S L34O0.SI 315 11 (RP 0) = true := by
  quickRfl

theorem kOrb1 : orbK 42 6 6 L34R.G GI (L34O.T 1) L34O1.E L34O1.S L34O1.SI 360 11 (RP 1) = true := by
  quickRfl

theorem kOrb2 : orbK 42 6 6 L34R.G GI (L34O.T 2) L34O2.E L34O2.S L34O2.SI 1008 11 (RP 2) = true := by
  quickRfl

theorem kOrb3 : orbK 42 6 6 L34R.G GI (L34O.T 3) L34O3.E L34O3.S L34O3.SI 280 11 (RP 3) = true := by
  quickRfl

theorem kR : (andB (Nat.beq (RP 0) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6)
      (pcomp 42 6 (mask 6) (L34R.G 0) (L34R.G 0)) (L34R.G 1)) (L34R.G 0)))
    (andB (Nat.beq (RP 1) (L34R.G 4)) (andB (Nat.beq (RP 2) (L34R.G 5))
      (Nat.beq (RP 3) (pcomp 42 6 (mask 6) (L34R.G 4) (L34R.G 5)))))) = true := by quickRfl

theorem kCanonR : allN 4 (fun j => canonK 42 6 (mask 6) (42 * 6) (RP j)) = true := by quickRfl

theorem kNorm : CFSG.KC.L34K.normK 42 6 6 L34R.G GI 3 L34R.G 20160 L34S.T (NWP 0) = true := by
  quickRfl

theorem kNotIn : (andB (notInK 20160 L34S.T (RP 1)) (andB (notInK 20160 L34S.T (RP 2))
    (notInK 20160 L34S.T (RP 3)))) = true := by quickRfl

theorem kCent1 : centK 42 6 20160 L34S.T (RP 0) 64 L34C1.X L34C1.P = true := by quickRfl

theorem kCent2 : centK 42 6 20160 L34S.T (RP 1) 168 L34C2.X L34C2.P = true := by quickRfl

theorem kCent3 : centK 42 6 20160 L34S.T (RP 2) 60 L34C3.X L34C3.P = true := by quickRfl

theorem kCent4 : centK 42 6 20160 L34S.T (RP 3) 72 L34C4.X L34C4.P = true := by quickRfl

theorem kGroup2 : groupK 42 6 168 L34C2.P L34C2.I L34C2.Q = true := by quickRfl

theorem kClass2 : classK 42 6 168 L34C2.P L34C2.I L34C2.CP (L34C2.L 0) (L34C2.L 1) (L34C2.L 2)
    (L34C2.L 3) 6 = true := by quickRfl

theorem kGroup3 : groupK 42 6 60 L34C3.P L34C3.I L34C3.Q = true := by quickRfl

theorem kClass3 : classK 42 6 60 L34C3.P L34C3.I L34C3.CP (L34C3.L 0) (L34C3.L 1) (L34C3.L 2)
    (L34C3.L 3) 5 = true := by quickRfl

theorem kDer1 : derK 42 6 72 L34C4.P L34C4.I 18 L34D1.P L34D1.PW L34D1.CW (L34D1.M 0) (L34D1.M 1) =
    true := by quickRfl

theorem kDer2 : derK 42 6 18 L34D1.P L34D1.I 9 L34D2.P L34D2.PW L34D2.CW (L34D2.M 0) (L34D2.M 1) =
    true := by quickRfl

theorem kDer3 : derK 42 6 9 L34D2.P L34D2.I 1 L34D3.P L34D3.PW L34D3.CW (L34D3.M 0) (L34D3.M 1) =
    true := by quickRfl

theorem kDisj : allN 4 (fun i => allN 4 fun j =>
    orB (Nat.beq i j) (notInK (L34O.N i) (L34O.T i) (RP j))) = true := by quickRfl

theorem kInvol : allN 4 (fun i => andB (Nat.beq (pcomp 42 6 (mask 6) (RP i) (RP i)) (pidn 42 6))
    (notB (Nat.beq (RP i) (pidn 42 6)))) = true := by quickRfl

end CertificateChecks.KernelLC

#kon_slices CertificateChecks.KernelLC.L34S.ps 0 15
#kon_join CertificateChecks.KernelLC.L34S.psAll CertificateChecks.KernelLC.L34S.ps 15

end
