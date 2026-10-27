module

public import Certificates.Kernel.Ru4120.Hall
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoRuPIdx2
import Certificates.Kernel.RuIdx2.L
public import Certificates.Data.Kernel.RuIdx2XK
public import Certificates.Kernel.RuIdx2.Defs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2.Sem

open CFSG.KD.RuIdx2 CFSG.KC.RuIdx2 CFSG.KC.Enum CFSG.KC.Kc3K CFSG.KD.Ru4120 CFSG.KS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.K1262Two.RuP

@[expose] def node (c : Nat) : Nat :=
  if c < 9 then [0, 1, 163, 172, 185, 198, 203, 207, 0].getD c 0 else 76

theorem node_lt (c : Nat) : node c < 486 := by
  unfold node
  split
  · rename_i h
    interval_cases c <;> decide
  · decide

theorem LC_eq (c : Nat) : LC c = TF (node c) := by
  rcases Nat.lt_or_ge c 9 with h | h
  · interval_cases c <;> rfl
  · have hb : ∀ k, k < 9 → Nat.beq c k = false := fun k hk =>
      Bool.eq_false_iff.2 fun h' => by have := Nat.eq_of_beq_eq_true h'; omega
    unfold LC node
    rw [if_neg (by omega), hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
      hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega), hb 8 (by omega)]

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 4060)] {a b : Γ}

@[expose] noncomputable def lt (a b : Γ) (c : Nat) : Γ := G.E a b (node c)

theorem act_let (h : H.Ctx a b) (c : Nat) {p : Nat} (hp : p < 4060) :
    act 4060 (lt a b c) p = pg 12 4095 (LC c) p := by
  rw [LC_eq]
  exact H.act_E h (node_lt c) hp

theorem rec_act (A : Nat → Nat → Nat) (e : Nat → Γ)
    (hA : ∀ c, ∀ q < 4060, A c q = act 4060 (e c) q) (F : Nat → Nat) :
    ∀ (n : Nat) {q : Nat}, q < 4060 →
      Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
        (fun k ih q => strictN (A (F k) q) ih) n q =
      act 4060 (((List.range n).map fun k => e (F k)).prod) q := by
  intro n
  induction n with
  | zero =>
    intro q hq
    simp [act_one hq]
  | succ n ih =>
    intro q hq
    simp only [Nat.rec_add_one, PK.strictN_eq]
    simp only [PK.strictN_eq] at ih
    rw [hA _ _ hq, ih (act_lt _ hq), List.range_succ, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, act_mul _ _ hq]

@[expose] noncomputable def wE (a b : Γ) (W : Nat) : Γ := ((unW W).map (lt a b)).prod

@[expose] noncomputable def letW (W i : Nat) : Nat :=
  fld(W, Nat.add (nat_lit 8) (Nat.shiftLeft i (nat_lit 2)), nat_lit 15)

@[expose] noncomputable def A0 (c q : Nat) : Nat := pg (nat_lit 12) (nat_lit 4095) (LC c) q

theorem A0_eq (h : H.Ctx a b) (c : Nat) {q : Nat} (hq : q < 4060) :
    A0 c q = act 4060 (lt a b c) q :=
  (act_let h c hq).symm

theorem unW_eq (W : Nat) : unW W = (List.range (Nat.land W 255)).map (letW W) := rfl

theorem wp_unfold (W q : Nat) : wp LC W q = Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => strictN (A0 (letW W k) q) ih) (Nat.land W 255) q := rfl

theorem wE_eq (W : Nat) :
    wE a b W = ((List.range (Nat.land W 255)).map fun k => lt a b (letW W k)).prod := by
  unfold wE
  rw [unW_eq, List.map_map, Function.comp_def]

theorem wp_eq (h : H.Ctx a b) (W : Nat) {q : Nat} (hq : q < 4060) :
    wp LC W q = act 4060 (wE a b W) q := by
  rw [wp_unfold, rec_act A0 (lt a b) (fun c q hq => A0_eq h c hq) (letW W) _ hq, wE_eq]

theorem prod_rev_inv (f g : Nat → Γ) : ∀ n, (∀ j < n, g j = (f j)⁻¹) →
    ((List.range n).map fun k => g (n - 1 - k)).prod = ((List.range n).map f).prod⁻¹
  | 0, _ => by simp
  | n + 1, hg => by
    have ih := prod_rev_inv f g n fun j hj => hg j (by omega)
    conv_rhs => rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, mul_inv_rev, ← ih]
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    congr 1
    · have e : n + 1 - 1 - 0 = n := by omega
      rw [e, hg n (by omega)]
    · refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
      have hk' : k < n := List.mem_range.1 hk
      have e : n + 1 - 1 - Nat.succ k = n - 1 - k := by omega
      simp only [Function.comp_apply, e]

theorem wpi_eq (h : H.Ctx a b) (hinv : ∀ c < 10, lt a b (IL c) = (lt a b c)⁻¹) (W : Nat)
    (hW : ∀ l ∈ unW W, l < 10) {q : Nat} (hq : q < 4060) :
    wpi LC IL W q = act 4060 (wE a b W)⁻¹ q := by
  have e : wpi LC IL W q = Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
      (fun k ih q => strictN (A0 (IL (letW W (Nat.land W 255 - 1 - k))) q) ih)
      (Nat.land W 255) q := rfl
  rw [e, rec_act A0 (lt a b) (fun c q hq => A0_eq h c hq) _ _ hq, wE_eq]
  congr 2
  exact prod_rev_inv (fun k => lt a b (letW W k)) (fun j => lt a b (IL (letW W j))) _
    fun j hj => hinv _ (hW _ (by rw [unW_eq]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))

@[expose] noncomputable def elE (a b : Γ) (RG : Nat → Nat) (nr X l : Nat) : Γ :=
  if l < nr then wE a b (RG l) else if l < nr + nr then (wE a b (RG (l - nr)))⁻¹ else
    if l = nr + nr then wE a b X else (wE a b X)⁻¹

theorem el_eq (h : H.Ctx a b) (hinv : ∀ c < 10, lt a b (IL c) = (lt a b c)⁻¹) (RG : Nat → Nat)
    (nr X : Nat) (hRG : ∀ l < nr, ∀ c ∈ unW (RG l), c < 10) (hX : ∀ c ∈ unW X, c < 10)
    (l : Nat) {q : Nat} (hq : q < 4060) :
    el LC IL RG nr X l q = act 4060 (elE a b RG nr X l) q := by
  unfold el elE
  simp only [PK.nIf_eq, Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq]
  split_ifs with h1 h2 h3
  · exact wp_eq h _ hq
  · exact wpi_eq h hinv _ (hRG _ (by omega)) hq
  · exact wp_eq h _ hq
  · exact wpi_eq h hinv _ hX hq

@[expose] noncomputable def epE (a b : Γ) (RG : Nat → Nat) (nr X E : Nat) : Γ :=
  ((List.range (Nat.land E 255)).map fun k => elE a b RG nr X (letW E k)).prod

theorem ep_unfold (RG : Nat → Nat) (nr X E q : Nat) : ep LC IL RG nr X E q =
    Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
      (fun k ih q => strictN (el LC IL RG nr X (letW E k) q) ih) (Nat.land E 255) q := rfl

theorem ep_eq (h : H.Ctx a b) (hinv : ∀ c < 10, lt a b (IL c) = (lt a b c)⁻¹) (RG : Nat → Nat)
    (nr X : Nat) (hRG : ∀ l < nr, ∀ c ∈ unW (RG l), c < 10) (hX : ∀ c ∈ unW X, c < 10)
    (E : Nat) {q : Nat} (hq : q < 4060) :
    ep LC IL RG nr X E q = act 4060 (epE a b RG nr X E) q := by
  rw [ep_unfold, rec_act (el LC IL RG nr X) (elE a b RG nr X)
    (fun c q hq => el_eq h hinv RG nr X hRG hX c hq) (letW E) _ hq]
  rfl

theorem epE_mem (R : Subgroup Γ) (RG : Nat → Nat) (nr X E : Nat)
    (hR : ∀ l < nr, wE a b (RG l) ∈ R) : epE a b RG nr X E ∈ R ⊔ Subgroup.zpowers (wE a b X) := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy
  unfold elE
  split_ifs with h1 h2 h3
  · exact Subgroup.mem_sup_left (hR _ h1)
  · exact Subgroup.mem_sup_left (R.inv_mem (hR _ (by omega)))
  · exact mem_sup_zpowers R _
  · exact Subgroup.inv_mem _ (mem_sup_zpowers R _)

theorem eq_of_Bs (h : H.Ctx a b) {g g' : Γ} (hg : ∀ p ∈ Bs, act 4060 g p = act 4060 g' p) :
    g = g' :=
  H.eq_of_base h hg

end Group

theorem psi_lt (k : Nat) : psi k < 8 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem labK_spec {k : Nat} (hk : k < 16384) :
    psi (tg 0 k) = Nat.xor (psi k) 1 ∧ psi (tg 1 k) = Nat.xor (psi k) 2 ∧
      psi (tg 2 k) = Nat.xor (psi k) 4 := by
  have h32 : k / 512 < 32 := by omega
  have h := L.all (k / 512) h32
  unfold famL at h
  have h1 := List.all_eq_true.1 h (k % 512) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  have e : Nat.add (Nat.mul (k / 512) 512) (k % 512) = k := by
    rw [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h1
  unfold labK at h1
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h1
  exact ⟨h1.1, h1.2.1, h1.2.2⟩

theorem par_xor : ∀ vm < 8, ∀ s < 8, ∀ c < 3,
    ((par vm (Nat.xor s (2 ^ c)) : Nat) : ZMod 2) =
      ((par vm s : Nat) : ZMod 2) + ((par vm (2 ^ c) : Nat) : ZMod 2) := by
  decide

end CFSG.KD.RuIdx2.Sem

end
