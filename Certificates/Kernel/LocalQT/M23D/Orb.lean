module

public import Certificates.Kernel.LocalQT.M23D.Gens
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.KD.LQT.M23D

open Equiv CFSG.QuasithinUnique.Vol2Native.L239.Covers CFSG.Sporadic.Schreier CFSG.Blueprint
open scoped Pointwise

@[expose] noncomputable def mergeD (l1 : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun l2 => l2)
    (fun a as ih l2 => List.rec (motive := fun _ => List ℕ) (a :: as)
      (fun b bs ihb => Bool.rec (motive := fun _ => List ℕ)
        (Bool.rec (motive := fun _ => List ℕ) (b :: ihb) (a :: ih bs) (Nat.beq a b))
        (a :: ih (b :: bs)) (Nat.blt a b)) l2) l1

theorem mem_mergeD (x : ℕ) (l1 : List ℕ) : ∀ l2, x ∈ mergeD l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  induction l1 with
  | nil => intro l2; simp only [List.not_mem_nil, false_or]; rfl
  | cons a as ih =>
    intro l2
    induction l2 with
    | nil => simp only [List.not_mem_nil, or_false]; rfl
    | cons b bs ihb =>
      change x ∈ Bool.rec (motive := fun _ => List ℕ)
        (Bool.rec (motive := fun _ => List ℕ) (b :: mergeD (a :: as) bs) (a :: mergeD as bs)
          (Nat.beq a b)) (a :: mergeD as (b :: bs)) (Nat.blt a b) ↔ _
      cases h1 : Nat.blt a b
      · cases h2 : Nat.beq a b
        · change x ∈ b :: mergeD (a :: as) bs ↔ _
          rw [List.mem_cons, ihb]
          simp only [List.mem_cons]
          tauto
        · have hab : a = b := Nat.eq_of_beq_eq_true h2
          subst hab
          change x ∈ a :: mergeD as bs ↔ _
          rw [List.mem_cons, ih]
          simp only [List.mem_cons]
          tauto
      · change x ∈ a :: mergeD as (b :: bs) ↔ _
        rw [List.mem_cons, ih]
        simp only [List.mem_cons]
        tauto

@[expose] noncomputable def passD (R : List (List ℕ)) : Option (List ℕ) → List (List ℕ) :=
  List.rec (motive := fun _ => Option (List ℕ) → List (List ℕ))
    (fun o => Option.rec (motive := fun _ => List (List ℕ)) [] (fun a => [a]) o)
    (fun r _ ih o => Option.rec (motive := fun _ => List (List ℕ)) (ih (some r))
      (fun a => mergeD a r :: ih none) o) R

theorem mem_passD (x : ℕ) (R : List (List ℕ)) : ∀ o : Option (List ℕ),
    x ∈ (passD R o).flatten ↔ x ∈ R.flatten ∨ x ∈ o.getD [] := by
  induction R with
  | nil =>
    intro o
    cases o with
    | none => change x ∈ ([] : List (List ℕ)).flatten ↔ _; simp
    | some a => change x ∈ [a].flatten ↔ _; simp
  | cons r R ih =>
    intro o
    cases o with
    | none =>
      change x ∈ (passD R (some r)).flatten ↔ _
      rw [ih]
      simp only [List.flatten_cons, List.mem_append, Option.getD_some, Option.getD_none,
        List.not_mem_nil, or_false]
      tauto
    | some a =>
      change x ∈ (mergeD a r :: passD R none).flatten ↔ _
      rw [List.flatten_cons, List.mem_append, mem_mergeD, ih]
      simp only [List.flatten_cons, List.mem_append, Option.getD_some, Option.getD_none,
        List.not_mem_nil, or_false]
      tauto

@[expose] noncomputable def flatK (R : List (List ℕ)) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun r _ ih => appK r ih) R

theorem flatK_eq (R : List (List ℕ)) : flatK R = R.flatten := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    change appK r (flatK R) = _
    rw [appK_eq, ih, List.flatten_cons]

@[expose] noncomputable def sortR (R : List (List ℕ)) (n : ℕ) : List ℕ :=
  flatK (Nat.rec (motive := fun _ => List (List ℕ)) R (fun _ R => passD R none) n)

theorem mem_sortR (x : ℕ) (R : List (List ℕ)) (n : ℕ) : x ∈ sortR R n ↔ x ∈ R.flatten := by
  unfold sortR
  rw [flatK_eq]
  induction n with
  | zero => rfl
  | succ n ih =>
    change x ∈ (passD (Nat.rec (motive := fun _ => List (List ℕ)) R
      (fun _ R => passD R none) n) none).flatten ↔ _
    rw [mem_passD, ih]
    simp

@[expose] noncomputable def runsK (f g : ℕ → ℕ) (S : List ℕ) : List (List ℕ) :=
  List.rec (motive := fun _ => List (List ℕ)) []
    (fun x _ ih => letN x fun x => letN (f x) fun y => letN (g x) fun z =>
      [x] :: [y] :: [z] :: ih) S

theorem mem_runsK (f g : ℕ → ℕ) (x : ℕ) (S : List ℕ) : x ∈ (runsK f g S).flatten ↔
    x ∈ S ∨ (∃ y ∈ S, f y = x) ∨ ∃ y ∈ S, g y = x := by
  induction S with
  | nil => simp [runsK]
  | cons y S ih =>
    change x ∈ (letN y fun x => letN (f x) fun y => letN (g x) fun z =>
      [x] :: [y] :: [z] :: runsK f g S).flatten ↔ _
    simp only [letN_eq, List.flatten_cons, List.mem_append, ih, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, @eq_comm _ x, or_assoc]
    constructor
    · rintro (h | h | h | h | h | h)
      exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
        Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inl h))),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]
    · rintro (h | h | h | h | h | h)
      exacts [Or.inl h, Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inl h),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))), Or.inr (Or.inr (Or.inl h)),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]

@[expose] noncomputable def vstepK (S : List ℕ) : List ℕ :=
  sortR (runsK (pm cA) (pm cBi) S) (nat_lit 12)

@[expose] noncomputable def bfsK (n : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [enc D23] (fun _ S => vstepK S) n

theorem pm_gM0 (t : Finset (Fin 23)) : pm cA (enc t) = enc (gM 0 • t) := pm_letter 0 true t

theorem pm_gM1 (t : Finset (Fin 23)) : pm cBi (enc t) = enc (gM 1 • t) := pm_letter 1 true t

theorem mem_bfsK (n : ℕ) : ∀ x, x ∈ bfsK n ↔ ∃ s ∈ bfs n, enc s = x := by
  induction n with
  | zero =>
    intro x
    change x ∈ [enc D23] ↔ ∃ s ∈ ({D23} : Finset (Finset (Fin 23))), enc s = x
    simp [eq_comm]
  | succ n ih =>
    intro x
    have hb : bfs (n + 1) = vstep (bfs n) := Function.iterate_succ_apply' _ _ _
    change x ∈ sortR (runsK (pm cA) (pm cBi) (bfsK n)) 12 ↔ _
    rw [mem_sortR, mem_runsK, hb]
    unfold vstep
    constructor
    · rintro (h | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · obtain ⟨s, hs, rfl⟩ := (ih x).1 h
        exact ⟨s, Finset.mem_union_left _ (Finset.mem_union_left _ hs), rfl⟩
      · obtain ⟨s, hs, rfl⟩ := (ih y).1 hy
        exact ⟨gM 0 • s, Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ hs)), (pm_gM0 s).symm⟩
      · obtain ⟨s, hs, rfl⟩ := (ih y).1 hy
        exact ⟨gM 1 • s, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs),
          (pm_gM1 s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      rcases Finset.mem_union.1 hs with hs | hs
      · rcases Finset.mem_union.1 hs with hs | hs
        · exact Or.inl ((ih _).2 ⟨s, hs, rfl⟩)
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
          exact Or.inr (Or.inl ⟨enc t, (ih _).2 ⟨t, ht, rfl⟩, pm_gM0 t⟩)
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
        exact Or.inr (Or.inr ⟨enc t, (ih _).2 ⟨t, ht, rfl⟩, pm_gM1 t⟩)

@[expose] noncomputable def dropThen (b : ℕ) (C : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) (k [])
    (fun c cs _ => Bool.rec (motive := fun _ => Bool) (k (c :: cs)) (k cs) (Nat.beq c b)) C

theorem dropThen_true {b : ℕ} {C : List ℕ} {k : List ℕ → Bool} (h : dropThen b C k = true) :
    ∃ C', k C' = true ∧ ∀ c ∈ C, c = b ∨ c ∈ C' := by
  cases C with
  | nil => exact ⟨[], h, by simp⟩
  | cons c cs =>
    change Bool.rec (motive := fun _ => Bool) (k (c :: cs)) (k cs) (Nat.beq c b) = true at h
    cases hc : Nat.beq c b
    · rw [hc] at h
      exact ⟨c :: cs, h, fun x hx => Or.inr hx⟩
    · rw [hc] at h
      refine ⟨cs, h, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl (Nat.eq_of_beq_eq_true hc)
      · exact Or.inr hx

@[expose] noncomputable def scanK (N : ℕ) (L : List ℕ) : ℕ → ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → List ℕ → Bool)
    (fun _ cnt C => Bool.and (Nat.beq cnt N) (isNilK C))
    (fun b _ ih prev cnt C => letN b fun b => letN cnt fun cnt =>
      Bool.and (Nat.blt prev b) (dropThen b C fun C' => ih b (Nat.succ cnt) C')) L

theorem scanK_true (N : ℕ) (L : List ℕ) : ∀ prev cnt C, scanK N L prev cnt C = true →
    (∀ x ∈ L, prev < x) ∧ L.Pairwise (· < ·) ∧ cnt + L.length = N ∧ ∀ c ∈ C, c ∈ L := by
  induction L with
  | nil =>
    intro prev cnt C h
    change Bool.and (Nat.beq cnt N) (isNilK C) = true at h
    rw [Bool.and_eq_true] at h
    have hC := isNilK_true h.2
    subst hC
    exact ⟨by simp, List.Pairwise.nil, by simpa using Nat.eq_of_beq_eq_true h.1, by simp⟩
  | cons b L ih =>
    intro prev cnt C h
    change (letN b fun b => letN cnt fun cnt => Bool.and (Nat.blt prev b)
      (dropThen b C fun C' => scanK N L b (Nat.succ cnt) C')) = true at h
    simp only [letN_eq, Bool.and_eq_true] at h
    have hpb : prev < b := Nat.blt_eq ▸ h.1
    obtain ⟨C', hC', hsub⟩ := dropThen_true h.2
    obtain ⟨hlt, hp, hc, hm⟩ := ih b (Nat.succ cnt) C' hC'
    refine ⟨fun x hx => ?_, List.pairwise_cons.2 ⟨hlt, hp⟩, ?_, fun c hc' => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact hpb
      · exact hpb.trans (hlt x hx)
    · simp only [List.length_cons]
      omega
    · rcases hsub c hc' with rfl | hc'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hm c hc')

@[expose] noncomputable def cellsOf (P : List (Finset (Fin 23) × Fin 9)) (R : List (List ℕ)) :
    List (List ℕ) :=
  List.rec (motive := fun _ => List (List ℕ)) R (fun p _ ih => letN (enc p.1) fun m => [m] :: ih) P

@[expose] noncomputable def cellRunsOf (K : List (Fin 7)) : List (List ℕ) :=
  List.rec (motive := fun _ => List (List ℕ)) [] (fun k _ ih => cellsOf (cycCells k) ih) K

@[expose] noncomputable def cellsK : List ℕ := sortR (cellRunsOf (List.finRange 7)) (nat_lit 6)

theorem mem_cellsOf (x : ℕ) (P : List (Finset (Fin 23) × Fin 9)) (R : List (List ℕ)) :
    x ∈ (cellsOf P R).flatten ↔ (∃ p ∈ P, enc p.1 = x) ∨ x ∈ R.flatten := by
  induction P with
  | nil => simp [cellsOf]
  | cons p P ih =>
    change x ∈ (letN (enc p.1) fun m => [m] :: cellsOf P R).flatten ↔ _
    rw [letN_eq, List.flatten_cons, List.mem_append, ih, List.mem_singleton]
    simp only [List.mem_cons, exists_eq_or_imp, @eq_comm _ x, or_assoc]

theorem enc_mem_cellRunsOf (K : List (Fin 7)) :
    ∀ k ∈ K, ∀ p ∈ cycCells k, enc p.1 ∈ (cellRunsOf K).flatten := by
  induction K with
  | nil => simp
  | cons k K ih =>
    intro k' hk p hp
    change enc p.1 ∈ (cellsOf (cycCells k) (cellRunsOf K)).flatten
    rw [mem_cellsOf]
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr (ih k' hk p hp)

theorem orbOK : scanK 1288 (bfsK 22) 0 0 cellsK = true := by
  quickRfl

theorem orbitCheck_eq : orbitCheck = true := by
  obtain ⟨-, hp, hc, hm⟩ := scanK_true 1288 (bfsK 22) 0 0 cellsK orbOK
  have himg : (bfs 22).image enc = (bfsK 22).toFinset := by
    ext x
    simp only [Finset.mem_image, List.mem_toFinset, mem_bfsK]
  have hcard : (bfs 22).card = 1288 := by
    rw [← Finset.card_image_of_injective _ enc_injective, himg,
      List.toFinset_card_of_nodup (hp.imp Nat.ne_of_lt)]
    omega
  have hcell : cellsIn (bfs 22) = true := by
    unfold cellsIn
    rw [List.all_eq_true]
    intro k hk
    rw [List.all_eq_true]
    intro p hp
    apply decide_eq_true
    have h1 : enc p.1 ∈ cellsK := (mem_sortR _ _ _).2 (enc_mem_cellRunsOf _ k hk p hp)
    obtain ⟨s, hs, hse⟩ := (mem_bfsK 22 _).1 (hm _ h1)
    rwa [← enc_injective hse]
  unfold orbitCheck
  simp [hcard, hcell]

end CFSG.KD.LQT.M23D
