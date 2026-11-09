module

public import CFSG.Certificates.Kernel.LocalQTLatSound
public import CFSG.Certificates.Kernel.LocalQTBfsKSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4125

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Bridge.Over.CertU33

abbrev WFK (S : SetK) : Prop := CFSG.KC.LQT.L.OrdN S.t ∧ ∀ x, memN S.t x ↔ x ∈ S.elems

abbrev GrowK (st st' : SetK × List ℕ) : Prop :=
  (∀ z, memN st.1.t z → memN st'.1.t z) ∧ (∀ z ∈ st'.1.elems, z ∈ st.1.elems ∨ z ∈ st'.2) ∧
    ∀ z ∈ st.2, z ∈ st'.2

theorem growK_refl (st : SetK × List ℕ) : GrowK st st :=
  ⟨fun _ h => h, fun _ h => Or.inl h, fun _ h => h⟩

theorem growK_trans {a b c : SetK × List ℕ} (h1 : GrowK a b) (h2 : GrowK b c) : GrowK a c := by
  refine ⟨fun z h => h2.1 z (h1.1 z h), fun z hz => ?_, fun z hz => h2.2.2 z (h1.2.2 z hz)⟩
  rcases h2.2.1 z hz with h | h
  · rcases h1.2.1 z h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h2.2.2 z h')
  · exact Or.inr h

theorem addK_spec {st : SetK × List ℕ} (hw : WFK st.1) (y : ℕ) :
    WFK (addK st y).1 ∧ GrowK st (addK st y) ∧ memN (addK st y).1.t y := by
  cases hm : memT st.1.t y with
  | true =>
    rw [addK_of_mem hm]
    exact ⟨hw, growK_refl st, (memT_iff hw.1 y).1 hm⟩
  | false =>
    rw [addK_of_not_mem hm]
    dsimp only
    refine ⟨⟨ord_insT y hw.1, fun x => ?_⟩, ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩, ?_⟩
    · rw [mem_insT, hw.2 x, List.mem_cons]
    · exact (mem_insT y z st.1.t).2 (Or.inr hz)
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact Or.inr (List.mem_cons.2 (Or.inl rfl))
      · exact Or.inl hz
    · exact List.mem_cons.2 (Or.inr hz)
    · exact (mem_insT y y st.1.t).2 (Or.inl rfl)

theorem innerK_spec (mf : ℕ → ℕ → ℕ) (x : ℕ) : ∀ (G : List ℕ) (st : SetK × List ℕ), WFK st.1 →
    WFK (G.foldl (fun st g => addK st (mf x g)) st).1 ∧
      GrowK st (G.foldl (fun st g => addK st (mf x g)) st) ∧
      ∀ g ∈ G, memN (G.foldl (fun st g => addK st (mf x g)) st).1.t (mf x g) := by
  intro G
  induction G with
  | nil => intro st hw; exact ⟨hw, growK_refl st, fun g hg => by simp at hg⟩
  | cons g G ih =>
    intro st hw
    obtain ⟨hw1, hg1, hm1⟩ := addK_spec hw (mf x g)
    obtain ⟨hw2, hg2, hm2⟩ := ih (addK st (mf x g)) hw1
    rw [List.foldl_cons]
    refine ⟨hw2, growK_trans hg1 hg2, fun g' hg' => ?_⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact hg2.1 _ hm1
    · exact hm2 g' hg'

theorem outerK_spec (mf : ℕ → ℕ → ℕ) (G : List ℕ) : ∀ (F : List ℕ) (st : SetK × List ℕ),
    WFK st.1 →
    WFK (F.foldl (fun st x => G.foldl (fun st g => addK st (mf x g)) st) st).1 ∧
      GrowK st (F.foldl (fun st x => G.foldl (fun st g => addK st (mf x g)) st) st) ∧
      ∀ x ∈ F, ∀ g ∈ G,
        memN (F.foldl (fun st x => G.foldl (fun st g => addK st (mf x g)) st) st).1.t (mf x g) := by
  intro F
  induction F with
  | nil => intro st hw; exact ⟨hw, growK_refl st, fun x hx => by simp at hx⟩
  | cons x F ih =>
    intro st hw
    obtain ⟨hw1, hg1, hm1⟩ := innerK_spec mf x G st hw
    obtain ⟨hw2, hg2, hm2⟩ := ih _ hw1
    rw [List.foldl_cons]
    refine ⟨hw2, growK_trans hg1 hg2, fun x' hx' g hg => ?_⟩
    rcases List.mem_cons.1 hx' with rfl | hx'
    · exact hg2.1 _ (hm1 g hg)
    · exact hm2 x' hx' g hg

abbrev InvK (mf : ℕ → ℕ → ℕ) (G : List ℕ) (o : ℕ) (st : SetK × List ℕ) : Prop :=
  WFK st.1 ∧ memN st.1.t o ∧ ∀ x ∈ st.1.elems, x ∈ st.2 ∨ ∀ g ∈ G, memN st.1.t (mf x g)

theorem roundK_inv (mf : ℕ → ℕ → ℕ) (G : List ℕ) {o : ℕ} {st : SetK × List ℕ}
    (h : InvK mf G o st) : InvK mf G o (roundG mf G st.1 st.2) := by
  obtain ⟨hw, ho, hc⟩ := h
  rw [roundG_eq]
  obtain ⟨hw', hg', hm'⟩ := outerK_spec mf G st.2 (st.1, []) hw
  refine ⟨hw', hg'.1 o ho, fun x hx => ?_⟩
  rcases hg'.2.1 x hx with hx0 | hx0
  · rcases hc x hx0 with hF | hcl
    · exact Or.inr (hm' x hF)
    · exact Or.inr fun g hg => hg'.1 _ (hcl g hg)
  · exact Or.inl hx0

@[expose] noncomputable def stK (mf : ℕ → ℕ → ℕ) (o : ℕ) (G : List ℕ) (d : ℕ) : SetK × List ℕ :=
  Nat.rec (motive := fun _ => SetK × List ℕ) (Prod.mk (SetK.mk (NT.nd NT.lf o NT.lf) 1 [o]) [o])
    (fun _ st => roundG mf G st.1 st.2) d

theorem stK_inv (mf : ℕ → ℕ → ℕ) (G : List ℕ) (o : ℕ) : ∀ d, InvK mf G o (stK mf o G d)
  | 0 => by
    refine ⟨⟨?_, fun x => ?_⟩, ?_, fun x hx => Or.inl hx⟩
    · show CFSG.KC.LQT.L.OrdN (NT.nd NT.lf o NT.lf)
      simp [CFSG.KC.LQT.L.OrdN, memN]
    · show memN (NT.nd NT.lf o NT.lf) x ↔ x ∈ [o]
      simp [memN]
    · show memN (NT.nd NT.lf o NT.lf) o
      simp [memN]
  | d + 1 => roundK_inv mf G (stK_inv mf G o d)

theorem closedG_of_stK (mf : ℕ → ℕ → ℕ) (G : List ℕ) {o d : ℕ} (h : (stK mf o G d).2 = []) :
    closedG mf o G (stK mf o G d).1 = true := by
  obtain ⟨hw, ho, hc⟩ := stK_inv mf G o d
  unfold closedG
  rw [CFSG.KC.LQT.P.andB_iff, memT_iff hw.1, CFSG.KC.LQT.P.allL_iff]
  refine ⟨ho, fun x hx => ?_⟩
  simp only [CFSG.KC.LQT.P.allL_iff, memT_iff hw.1]
  intro g hg
  rcases hc x hx with hF | hcl
  · rw [h] at hF
    simp at hF
  · exact hcl g hg

@[expose] noncomputable def doneK (n : ℕ) (G : List ℕ) (d : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false)
    (stK (CFSG.KC.LQT.P.mul n) (CFSG.KC.LQT.P.one n) G d).2

theorem closedK_of_doneK {n d : ℕ} {G : List ℕ} (h : doneK n G d = true) :
    closedK n G (bfsK n G d) = true := by
  have h2 : (stK (CFSG.KC.LQT.P.mul n) (CFSG.KC.LQT.P.one n) G d).2 = [] := by
    unfold doneK at h
    revert h
    cases (stK (CFSG.KC.LQT.P.mul n) (CFSG.KC.LQT.P.one n) G d).2 with
    | nil => intro _; rfl
    | cons a l => intro h; exact absurd h Bool.false_ne_true
  exact closedG_of_stK (CFSG.KC.LQT.P.mul n) G h2

theorem allA_iff' {α : Type} (l : List α) (f : α → Bool) :
    allA l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allA]
  | cons x l ih =>
    change CFSG.KC.Ord.andB (f x) (allA l f) = true ↔ _
    rw [CFSG.KC.LQT.P.andB_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem recMap' {α β : Type} (f : α → β) : ∀ l : List α,
    List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l = l.map f
  | [] => rfl
  | x :: l => by
    change f x :: List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l = _
    rw [recMap' f l, List.map_cons]

theorem closedOKK_of_done {n d : ℕ} {MG T : List ℕ} {lat : List (List ℕ)}
    (h : ∀ L ∈ MG :: T :: lat, doneK n L d = true) : closedOKK n d MG T lat = true := by
  have hmem : membersK n d T lat = (T :: lat).map (fun L => (L, bfsK n L d)) :=
    recMap' (fun L => (L, bfsK n L d)) (T :: lat)
  unfold closedOKK
  rw [CFSG.KC.LQT.P.andB_iff, allA_iff', hmem]
  refine ⟨closedK_of_doneK (h MG (List.mem_cons.2 (Or.inl rfl))), fun p hp => ?_⟩
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hp
  exact closedK_of_doneK (h L (List.mem_cons.2 (Or.inr hL)))

theorem p1_done : allA (cert.mGens.map code :: cert.tGens.map code :: cert.lat.map (List.map code))
    (fun L => doneK 28 L cert.depth) = true := by quickRfl
theorem p1 : closedOKK 28 cert.depth (cert.mGens.map code) (cert.tGens.map code)
    (cert.lat.map (List.map code)) = true :=
  closedOKK_of_done ((allA_iff' _ _).1 p1_done)
theorem p2 : coverK 28 cert.depth (cert.mGens.map code) (cert.tGens.map code) (repsCode cert) =
    true := by quickRfl
theorem p3 : repsK 28 (cert.tGens.map code)
    (membersK 28 cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)))
    (repsCode cert) = true := by quickRfl
theorem p4 : joinsK 28
    (membersK 28 cert.depth (cert.tGens.map code) (cert.lat.map (List.map code)))
    cert.joins = true := by quickRfl
theorem p5 : sizesK 28 cert.depth (cert.mGens.map code) (cert.tGens.map code)
    (cert.lat.map (List.map code)) cert.sizes cert.msize = true := by quickRfl
theorem p6 : tleK 28 cert.depth (cert.mGens.map code) (cert.tGens.map code) = true := by
  quickRfl
theorem hl : latK 28 cert.depth (cert.mGens.map code) (cert.tGens.map code)
    (cert.lat.map (List.map code)) (repsCode cert) cert.joins cert.sizes cert.msize = true :=
  latK_intro p1 p2 p3 p4 p5 p6
theorem hm : memberK 28 cert.depth (cert.tGens.map code) (cert.lat.map (List.map code))
    cert.msize (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo)) =
    true := by
  quickRfl

end CFSG.KD.LQT.C4125

end
