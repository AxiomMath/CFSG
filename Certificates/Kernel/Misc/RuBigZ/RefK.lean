module

public import Certificates.Data.Kernel.Misc.RuBigZR
public import Certificates.Data.Kernel.Misc.RuScanC
public import Certificates.Kernel.Misc.RuBigZ.Data
public import Certificates.Kernel.Misc.RuBigZ.DataE
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Quasithin.Vol2.KGFactC31RuRefData
public import CFSG.Quasithin.Vol2.KGFactC31RuData
public import CFSG.Sporadic.Schreier.RuData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan CFSG.KC.Misc.RuBigZ
  CertificateChecks.KernelSporSch CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier

@[expose] noncomputable def A6 : Nat → Nat → Nat :=
  pkA (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1)

@[expose] noncomputable def A6I : Nat → Nat → Nat :=
  pkA (gen6 RuG.A0I RuG.A1I RuG.C0I RuG.C1I RuG.Ns0I RuG.Ns1I)

@[expose] noncomputable def wF (w : List Int) : Nat → Nat := wAp A6 A6I w

@[expose] noncomputable def wFI (w : List Int) : Nat → Nat := wApI A6 A6I w

@[expose] noncomputable def zI : Nat := img4 (apP RuG.Z)

@[expose] noncomputable def ch7233eb : Bool :=
  bAnd(ebB R 0 3, bAnd(ebB R 3 6, bAnd(ebB R 9 3, bAnd(ebB R 12 4, bAnd(ebB R 16 5,
    bAnd(ebB Q 0 5, ebB Q 5 5))))))

@[expose] noncomputable def ch7233zs : Bool :=
  strictB zI (fun u => bAnd(inSp R 0 3 u, bAnd(inSp R 3 6 u, bAnd(inSp R 9 3 u,
    bAnd(inSp R 12 4 u, inSp R 16 5 u)))))

@[expose] noncomputable def ch7233ev : Bool :=
  allN 3 (fun i => inSp Q 0 5 (img4 (apP (R i))))

@[expose] noncomputable def ch7233fe : Bool :=
  allN 7 (fun m => Nat.beq (fixC (mAp R 0 3 (Nat.succ m))) 92)

@[expose] noncomputable def ch7233fv : Bool :=
  allN 31 (fun m => strictB (Nat.succ m) (fun m' =>
    bIf(inSp R 0 3 (mImg Q 0 5 m'), true, Nat.beq (fixC (mAp Q 0 5 m')) 0)))

@[expose] noncomputable def ch7233nx : Bool := normB R 12 4 (apP (Q 12)) (apP (Q 13))

@[expose] noncomputable def ch7233nc : Bool :=
  bAnd(normB R 16 5 (apP RuG.C0) (apP RuG.C0I), normB R 16 5 (apP RuG.C1) (apP RuG.C1I))

@[expose] noncomputable def ch7233or : Bool :=
  bAnd(ordB (apP (Q 10)) 7, bAnd(ordB (apP (Q 12)) 5, ordB (apP (Q 14)) 5))

@[expose] noncomputable def ch7233gx : Bool :=
  bIf(normB R 12 4 (fun x => apP (Q 16) (apP (Q 12) (apP (Q 17) x)))
    (fun x => apP (Q 16) (apP (Q 13) (apP (Q 17) x))), false, true)

@[expose] noncomputable def ch7233kv : Bool :=
  allN 5 (fun i => strictB (R (Nat.add 16 i)) (fun v =>
    inSp Q 5 5 (img4 (fun x => wF k16W (apP v (wFI k16W x))))))

@[expose] noncomputable def ch7233cd_ (i : Nat) : Bool :=
  allN 20 (fun j => bIf(Nat.beq i j, true,
    anyK 6 (fun k => strictB (R (Nat.add 3 k)) (fun v =>
      bIf(inSp R 3 6 (img4 (fun x => wFI (conj64W.getD j []) (wF (conj64W.getD i [])
        (apP v (wFI (conj64W.getD i []) (wF (conj64W.getD j []) x)))))), false, true)))))

@[expose] noncomputable def kF (a : Nat) : Nat → Nat :=
  wAp (pkA (gen2 RuG.Ns0 RuG.Ns1)) (pkA (gen2 RuG.Ns0I RuG.Ns1I)) (ruKWords.getD a [])

@[expose] noncomputable def kFI (a : Nat) : Nat → Nat :=
  wApI (pkA (gen2 RuG.Ns0 RuG.Ns1)) (pkA (gen2 RuG.Ns0I RuG.Ns1I)) (ruKWords.getD a [])

@[expose] noncomputable def ch7233ke : Bool :=
  allN 8 (fun a => bAnd(inSp R 0 3 (img4 (fun x => kF a (kF a x))),
    allN 8 (fun b => inSp R 0 3 (img4 (commF (kF a) (kFI a) (kF b) (kFI b))))))

@[expose] noncomputable def ch7233kb : Bool :=
  bAnd(Nat.beq (img4 (commF (kF 3) (kFI 3) (kF 4) (kFI 4))) (img4 (apP (R 0))),
  bAnd(Nat.beq (img4 (commF (kF 3) (kFI 3) (kF 1) (kFI 1))) (img4 (apP (R 1))),
    Nat.beq (img4 (commF (kF 4) (kFI 4) (kF 0) (kFI 0))) (img4 (apP (R 2)))))

@[expose] noncomputable def AX (k x : Nat) : Nat :=
  nIf(Nat.beq k 0, apP (Q 10) x, wF nEW (apP (Q 10) (wFI nEW x)))

@[expose] noncomputable def AXI (k x : Nat) : Nat :=
  nIf(Nat.beq k 0, apP (Q 11) x, wF nEW (apP (Q 11) (wFI nEW x)))

@[expose] noncomputable def ch7233ns : Bool :=
  bAnd(Nat.beq (img4 (wAp AX AXI (nsInXW.getD 0 []))) (img4 (apP RuG.Ns0)),
    Nat.beq (img4 (wAp AX AXI (nsInXW.getD 1 []))) (img4 (apP RuG.Ns1)))

@[expose] noncomputable def ch7233cq : Bool :=
  anyK 5 (fun i => strictB (R (Nat.add 16 i)) (fun v =>
    bIf(Nat.beq (img4 (fun x => commF (apP (Q 14)) (apP (Q 15)) (wF cQW) (wFI cQW) (apP v x)))
      (img4 (fun x => apP v (commF (apP (Q 14)) (apP (Q 15)) (wF cQW) (wFI cQW) x))), false, true)))

@[expose] noncomputable def jA (k x : Nat) : Nat :=
  wAp (pkA (gen2 RuG.C0 RuG.C1)) (pkA (gen2 RuG.C0I RuG.C1I)) (ruJWords.getD k []) x

@[expose] noncomputable def jAI (k x : Nat) : Nat :=
  wApI (pkA (gen2 RuG.C0 RuG.C1)) (pkA (gen2 RuG.C0I RuG.C1I)) (ruJWords.getD k []) x

@[expose] def cQJW : List Int := [1, 3, 5, 6, -5, 6]

@[expose] noncomputable def ch7233cj : Bool :=
  Nat.beq (img4 (wAp jA jAI cQJW)) (img4 (wF cQW))

@[expose] def eNW : List (List Int) := [[2], [], [1, 2]]

@[expose] noncomputable def ch7233ee : Bool :=
  allN 3 (fun k => Nat.beq (img4 (apP (R k)))
    (img4 (fun x => wAp (pkA (gen2 RuG.Ns0 RuG.Ns1)) (pkA (gen2 RuG.Ns0I RuG.Ns1I)) (eNW.getD k [])
      (apP RuG.Z (wApI (pkA (gen2 RuG.Ns0 RuG.Ns1)) (pkA (gen2 RuG.Ns0I RuG.Ns1I))
        (eNW.getD k []) x)))))

@[expose] noncomputable def rt (x : Nat) : Nat :=
  wF (hWordsZ.getD 0 []) (apP RuG.Z (wFI (hWordsZ.getD 0 []) x))

@[expose] noncomputable def ch7233r30 : Bool :=
  allN 31 (fun m => strictB (mImg R 16 5 (Nat.succ m)) (fun u =>
    bIf(Nat.beq u zI, true,
      anyK 30 (fun w => Nat.beq (img4 (fun x =>
        wF (conj30W.getD w []) (rt (wFI (conj30W.getD w []) x)))) u))))

end CertificateChecks.KernelMisc.RuBigZ

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233eb_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233eb = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233zs_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233zs = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233ev_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233ev = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233fe_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233fe = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233fv_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233fv = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233nx_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233nx = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233nc_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233nc = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233or_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233or = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233gx_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233gx = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233kv_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233kv = true := by quickRfl

#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233cd_ 0 20

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233ke_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233ke = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233kb_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233kb = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233ns_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233ns = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233cq_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233cq = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233cj_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233cj = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233ee_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233ee = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233r30_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233r30 = true := by quickRfl

end
