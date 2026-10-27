
module

public import Certificates.Kernel.LocalComp.L34RChk0
public import Certificates.Kernel.LocalComp.L34RChk1
public import Certificates.Kernel.LocalComp.L34RChk2
public import Certificates.Kernel.LocalComp.L34RChk3
public import Certificates.Kernel.LocalComp.L34SChk
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.L34KSound
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeAutKSound

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelLC.L34R.prAll CertificateChecks.KernelLC.L34R.pr 180
#kon_join CertificateChecks.KernelLC.L34R.rpAll CertificateChecks.KernelLC.L34R.rp 180

namespace CertificateChecks.KernelLC.L34Cert

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.PermTool
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X CFSG.PSL3Four.Native
open CFSG.KLie.CT (fget)

theorem bindR : gTabs.size = 6 ∧ ∀ k < 6, gTabs[k]! = unpack 42 6 (L34R.G k) := binds_of_check kBindR

theorem bindS : gensS.size = 3 ∧ ∀ k < 3, gensS[k]! = unpack 42 6 (L34R.G k) :=
  binds_of_check kBindS

theorem pinR : PinE 42 6 gTabs 241920 6 241920 1344 180 18 L34R.G L34R.T L34R.E L34R.C L34R.S
    L34R.SI :=
  ⟨bindR.1, bindR.2, allN_spec kPermR, kHeadR, by decide, by decide, le_refl _,
    fun s hs => L34R.prAll s hs⟩

theorem pinS : PinE 42 6 gensS 20160 3 20160 1344 15 18 L34R.G L34S.T L34S.E L34S.C L34S.S
    L34S.SI :=
  ⟨bindS.1, bindS.2, fun k hk => allN_spec kPermR k (by omega), kHeadS, by decide, by decide,
    le_refl _, fun s hs => L34S.psAll s hs⟩

theorem cnG {k : Nat} (hk : k < 6) : canonK 42 6 (mask 6) (42 * 6) (L34R.G k) = true :=
  pinR.canonG k hk

theorem g_eq {k : Nat} (hk : k < 6) : gTabs[k]! = unpack 42 6 (L34R.G k) := bindR.2 k hk

theorem cnRP {j : Nat} (hj : j < 4) : canonK 42 6 (mask 6) (42 * 6) (RP j) = true :=
  allN_spec kCanonR j hj

theorem kRs : RP 0 = pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34R.G 0)
      (L34R.G 0)) (L34R.G 1)) (L34R.G 0) ∧ RP 1 = L34R.G 4 ∧ RP 2 = L34R.G 5 ∧
    RP 3 = pcomp 42 6 (mask 6) (L34R.G 4) (L34R.G 5) := by
  obtain ⟨h0, h⟩ := andT kR
  obtain ⟨h1, h⟩ := andT h
  obtain ⟨h2, h3⟩ := andT h
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3⟩

theorem e1 : g₁T = unpack 42 6 (L34R.G 0) := g_eq (k := 0) (by decide)
theorem e2 : g₂T = unpack 42 6 (L34R.G 1) := g_eq (k := 1) (by decide)
theorem e5 : g₅T = unpack 42 6 (L34R.G 4) := g_eq (k := 4) (by decide)
theorem e6 : g₆T = unpack 42 6 (L34R.G 5) := g_eq (k := 5) (by decide)

theorem r1_eq : r₁T () = unpack 42 6 (RP 0) := by
  rw [kRs.1]
  unfold r₁T
  rw [e1, e2, comp_eq, comp_eq, comp_eq, compA_unpack (cnG (by decide)) (cnG (by decide)),
    compA_unpack (canonK_pcomp (cnG (by decide)) (cnG (by decide))) (cnG (by decide)),
    compA_unpack (canonK_pcomp (canonK_pcomp (cnG (by decide)) (cnG (by decide)))
      (cnG (by decide))) (cnG (by decide))]

theorem r2_eq : r₂T = unpack 42 6 (RP 1) := by rw [kRs.2.1, r₂T, e5]

theorem r3_eq : r₃T = unpack 42 6 (RP 2) := by rw [kRs.2.2.1, r₃T, e6]

theorem r4_eq : r₄T () = unpack 42 6 (RP 3) := by
  rw [kRs.2.2.2]
  unfold r₄T
  rw [e5, e6, comp_eq, compA_unpack (cnG (by decide)) (cnG (by decide))]

theorem hrs : (rTabs ()).size = 4 ∧ ∀ j < 4, (rTabs ())[j]! = unpack 42 6 (RP j) ∧
    canonK 42 6 (mask 6) (42 * 6) (RP j) = true := by
  refine ⟨rfl, fun j hj => ⟨?_, cnRP hj⟩⟩
  match j, hj with
  | 0, _ => simpa [rTabs] using r1_eq
  | 1, _ => simpa [rTabs] using r2_eq
  | 2, _ => simpa [rTabs] using r3_eq
  | 3, _ => simpa [rTabs] using r4_eq

theorem pinO0 : PinO 42 6 gTabs (r₁T ()) 1963 6 315 11 (RP 0) L34R.G GI (L34O.T 0) L34O0.E
    L34O0.S L34O0.SI := ⟨bindR.1, bindR.2, r1_eq, kOrb0, by decide⟩

theorem pinO1 : PinO 42 6 gTabs r₂T 1963 6 360 11 (RP 1) L34R.G GI (L34O.T 1) L34O1.E
    L34O1.S L34O1.SI := ⟨bindR.1, bindR.2, r2_eq, kOrb1, by decide⟩

theorem pinO2 : PinO 42 6 gTabs r₃T 1963 6 1008 11 (RP 2) L34R.G GI (L34O.T 2) L34O2.E
    L34O2.S L34O2.SI := ⟨bindR.1, bindR.2, r3_eq, kOrb2, by decide⟩

theorem pinO3 : PinO 42 6 gTabs (r₄T ()) 1963 6 280 11 (RP 3) L34R.G GI (L34O.T 3) L34O3.E
    L34O3.S L34O3.SI := ⟨bindR.1, bindR.2, r4_eq, kOrb3, by decide⟩

theorem hS : (enumBFS 42 gensS 20160).tabs = pts 42 6 20160 L34S.T ∧
    enumOK 42 gensS (enumBFS 42 gensS 20160) = true := enum_sound pinS

theorem hR : (enumBFS 42 gTabs 241920).tabs = pts 42 6 241920 L34R.T ∧
    enumOK 42 gTabs (enumBFS 42 gTabs 241920) = true := enum_sound pinR

theorem hO0 : (orbitBFS 42 gTabs (gTabs.map (invTab 42)) (r₁T ()) 1963).tabs =
      pts 42 6 315 (L34O.T 0) ∧
    orbitOK 42 gTabs (gTabs.map (invTab 42)) (r₁T ())
      (orbitBFS 42 gTabs (gTabs.map (invTab 42)) (r₁T ()) 1963) = true := orbit_sound pinO0

theorem hO1 : (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₂T 1963).tabs =
      pts 42 6 360 (L34O.T 1) ∧
    orbitOK 42 gTabs (gTabs.map (invTab 42)) r₂T
      (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₂T 1963) = true := orbit_sound pinO1

theorem hO2 : (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₃T 1963).tabs =
      pts 42 6 1008 (L34O.T 2) ∧
    orbitOK 42 gTabs (gTabs.map (invTab 42)) r₃T
      (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₃T 1963) = true := orbit_sound pinO2

theorem hO3 : (orbitBFS 42 gTabs (gTabs.map (invTab 42)) (r₄T ()) 1963).tabs =
      pts 42 6 280 (L34O.T 3) ∧
    orbitOK 42 gTabs (gTabs.map (invTab 42)) (r₄T ())
      (orbitBFS 42 gTabs (gTabs.map (invTab 42)) (r₄T ()) 1963) = true := orbit_sound pinO3

theorem hOA : (#[pts 42 6 315 (L34O.T 0), pts 42 6 360 (L34O.T 1), pts 42 6 1008 (L34O.T 2),
    pts 42 6 280 (L34O.T 3)] : Array (Array Tab)).size = 4 ∧
    ∀ o < 4, (#[pts 42 6 315 (L34O.T 0), pts 42 6 360 (L34O.T 1), pts 42 6 1008 (L34O.T 2),
      pts 42 6 280 (L34O.T 3)] : Array (Array Tab))[o]! = pts 42 6 (L34O.N o) (L34O.T o) := by
  refine ⟨rfl, fun o ho => ?_⟩
  match o, ho with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem hOc : ∀ o < 4, ∀ i < L34O.N o, canonK 42 6 (mask 6) (42 * 6) (L34O.T o i) = true := by
  intro o ho
  match o, ho with
  | 0, _ => exact pinO0.canon
  | 1, _ => exact pinO1.canon
  | 2, _ => exact pinO2.canon
  | 3, _ => exact pinO3.canon

theorem cent1 : centTabs 42 (pts 42 6 20160 L34S.T) (r₁T ()) = pts 42 6 64 L34C1.P :=
  cent_sound r1_eq (cnRP (by decide)) pinS.canon kCent1
theorem cent2 : centTabs 42 (pts 42 6 20160 L34S.T) r₂T = pts 42 6 168 L34C2.P :=
  cent_sound r2_eq (cnRP (by decide)) pinS.canon kCent2
theorem cent3 : centTabs 42 (pts 42 6 20160 L34S.T) r₃T = pts 42 6 60 L34C3.P :=
  cent_sound r3_eq (cnRP (by decide)) pinS.canon kCent3
theorem cent4 : centTabs 42 (pts 42 6 20160 L34S.T) (r₄T ()) = pts 42 6 72 L34C4.P :=
  cent_sound r4_eq (cnRP (by decide)) pinS.canon kCent4

@[expose] noncomputable def DD1 : Array Tab × Array (ℕ × ℕ × ℕ × ℕ) :=
  derivedData 42 (pts 42 6 72 L34C4.P) ((pts 42 6 72 L34C4.P).map (invTab 42))

@[expose] noncomputable def DD2 : Array Tab × Array (ℕ × ℕ × ℕ × ℕ) :=
  derivedData 42 DD1.1 (DD1.1.map (invTab 42))

theorem der1 : derivedOK 42 (pts 42 6 72 L34C4.P) ((pts 42 6 72 L34C4.P).map (invTab 42))
      DD1.1 DD1.2 = true ∧ DD1.1.size = 18 ∧
    ∀ x, x ∈ DD1.1.toList ↔ x ∈ (pts 42 6 18 L34D1.P).toList :=
  der_sound (A := pts 42 6 72 L34C4.P) (fun _ => Iff.rfl) kDer1

theorem der2 : derivedOK 42 DD1.1 (DD1.1.map (invTab 42)) DD2.1 DD2.2 = true ∧
    DD2.1.size = 9 ∧ ∀ x, x ∈ DD2.1.toList ↔ x ∈ (pts 42 6 9 L34D2.P).toList :=
  der_sound (A := DD1.1) der1.2.2 kDer2

theorem der3 : derivedOK 42 DD2.1 (DD2.1.map (invTab 42))
      (derivedData 42 DD2.1 (DD2.1.map (invTab 42))).1
      (derivedData 42 DD2.1 (DD2.1.map (invTab 42))).2 = true ∧
    (derivedData 42 DD2.1 (DD2.1.map (invTab 42))).1.size = 1 ∧
    ∀ x, x ∈ (derivedData 42 DD2.1 (DD2.1.map (invTab 42))).1.toList ↔
      x ∈ (pts 42 6 1 L34D3.P).toList :=
  der_sound (A := DD2.1) der2.2.2 kDer3

theorem notIns : notInK 20160 L34S.T (RP 1) = true ∧ notInK 20160 L34S.T (RP 2) = true ∧
    notInK 20160 L34S.T (RP 3) = true := by
  obtain ⟨h1, h⟩ := andT kNotIn
  exact ⟨h1, andT h⟩

theorem certificate_true : certificate 20160 241920 1963 = true := by
  simp only [certificate, Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨hS.2, ?_, hR.2, ?_, ?_, ?_, hO0.2, hO1.2, hO2.2, hO3.2, ?_, ?_, ?_, ?_, ?_, ?_,
    involution_sound hrs kInvol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS.1, size_pts]
  · rw [hR.1, size_pts]
  · rw [hS.1]
    exact normal_sound bindR bindS kNorm
  · rw [hR.1]
    exact (rpass_sound bindS (fun k hk => cnG (by omega)) hOA pinR.canon (by decide) L34R.rpAll).1
  · rw [hO0.1, size_pts]
  · rw [hO1.1, size_pts]
  · rw [hO2.1, size_pts]
  · rw [hO3.1, size_pts]
  · rw [hR.1, hO0.1, hO1.1, hO2.1, hO3.1]
    exact (rpass_sound bindS (fun k hk => cnG (by omega)) hOA pinR.canon (by decide) L34R.rpAll).2
  · rw [hO0.1, hO1.1, hO2.1, hO3.1]
    exact disjoint_sound hOA hrs hOc kDisj
  · rw [hS.1]
    exact notIn_sound r2_eq (cnRP (by decide)) pinS.canon notIns.1
  · rw [hS.1]
    exact notIn_sound r3_eq (cnRP (by decide)) pinS.canon notIns.2.1
  · rw [hS.1]
    exact notIn_sound (r4_eq) (cnRP (by decide)) pinS.canon notIns.2.2
  · rw [hS.1, cent1, size_pts]
  · rw [hS.1, cent2, size_pts]
  · rw [hS.1, cent3, size_pts]
  · rw [hS.1, cent4, size_pts]
  · rw [hS.1, cent2]
    exact class_sound ⟨rfl, by decide +kernel⟩ kGroup2 kClass2
  · rw [hS.1, cent3]
    exact class_sound ⟨rfl, by decide +kernel⟩ kGroup3 kClass3
  · rw [hS.1, cent4]
    exact der1.1
  · rw [hS.1, cent4]
    exact der1.2.1
  · rw [hS.1, cent4]
    exact der2.1
  · rw [hS.1, cent4]
    exact der2.2.1
  · rw [hS.1, cent4]
    exact der3.1
  · rw [hS.1, cent4]
    exact der3.2.1

end CertificateChecks.KernelLC.L34Cert

end
