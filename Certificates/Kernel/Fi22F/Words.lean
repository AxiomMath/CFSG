module

public import Certificates.Data.Kernel.Fi22F.Walks
public import CFSG.Certificates.Kernel.HOrbSound
public import Certificates.Kernel.Co2.Words

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CFSG.KC.Fi22F.Walks
  CFSG.Sporadic.Presentation.Fi22Exact CertificateChecks.KernelCo2

theorem andB_eq' (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem digits_cons (c : ℕ) (l : List ℕ) : digits (c :: l) = c + digits l * 256 ^ 1 := by
  change c + 256 * digits l = _
  ring

theorem digits_lt (l : List ℕ) (h : ∀ c ∈ l, c < 256) : digits l < 256 ^ l.length := by
  induction l with
  | nil => change 0 < 1; norm_num
  | cons c l ih =>
    rw [digits_cons, List.length_cons, pow_one, pow_succ]
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h c (List.mem_cons_self)
    have h3 : digits l + 1 ≤ 256 ^ l.length := h1
    nlinarith

theorem bval_digits {G : Type*} [Group G] (gen : ℕ → G) (l : List ℕ) (h : ∀ c ∈ l, c < 256) :
    bval gen (digits l) l.length = (l.map (letV gen)).prod := by
  induction l with
  | nil => exact HO.bval_zero gen _
  | cons c l ih =>
    have hc := h c List.mem_cons_self
    have e := HO.bval_concat gen (A := c) (B := digits l) (p := 1) (q := l.length) (by rw [pow_one]; exact hc)
    rw [digits_cons, List.length_cons, Nat.add_comm l.length 1, e, HO.bval_one gen hc,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx), List.map_cons, List.prod_cons]

theorem wWord_entL (l : List ℕ) (hl : l.length < 1024) : wWord (entL l) = digits l := by
  change (4 * l.length + 4096 * digits l) >>> 12 = _
  rw [Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem wLen_entL (l : List ℕ) (hl : l.length < 1024) : wLen (entL l) = l.length := by
  change ((4 * l.length + 4096 * digits l) >>> 2) &&& (2 ^ 10 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  omega

theorem bval_entL {G : Type*} [Group G] (gen : ℕ → G) (l : List ℕ) (hl : l.length < 1024)
    (h : ∀ c ∈ l, c < 256) : bval gen (wWord (entL l)) (wLen (entL l)) = (l.map (letV gen)).prod := by
  rw [wWord_entL l hl, wLen_entL l hl, bval_digits gen l h]

theorem entW_eq (l : List ℕ) :
    entW l = 4 * l.length + 4096 * (digits l + 1 * 256 ^ l.length) := by
  change 4 * l.length + 4096 * digits l + 1 <<< (12 + 8 * l.length) = _
  rw [Nat.one_shiftLeft, pow_add, pow_mul]
  ring

theorem bval_entW {G : Type*} [Group G] (gen : ℕ → G) (l : List ℕ) (hl : l.length < 1024)
    (h : ∀ c ∈ l, c < 256) : bval gen (wWord (entW l)) (wLen (entW l)) = (l.map (letV gen)).prod := by
  have hw : wWord (entW l) = digits l + 1 * 256 ^ l.length := by
    rw [entW_eq]
    change (4 * l.length + 4096 * (digits l + 1 * 256 ^ l.length)) >>> 12 = _
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have hn : wLen (entW l) = l.length + 0 := by
    rw [entW_eq]
    change ((4 * l.length + 4096 * (digits l + 1 * 256 ^ l.length)) >>> 2) &&& (2 ^ 10 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    omega
  rw [hw, hn, HO.bval_concat gen (digits_lt l h), HO.bval_zero, mul_one, bval_digits gen l h]

theorem relsBind_spec {RT : ℕ → ℕ} {ws : List (List (Fin 6 × Bool))} {k₀ : ℕ}
    (h : relsBind RT ws k₀ = true) : ∀ k < ws.length, RT (k₀ + k) = entL ((ws.getD k []).map code) := by
  induction ws generalizing k₀ with
  | nil => intro k hk; cases hk
  | cons w ws ih =>
    have h' : andB (Nat.beq (RT k₀) (entL (w.map code))) (relsBind RT ws (Nat.succ k₀)) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    intro k hk
    cases k with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ k =>
      have := ih h2 k (by simpa using hk)
      rw [show k₀ + (k + 1) = Nat.succ k₀ + k by omega, this]
      rfl

theorem posBind_spec {ST : ℕ → ℕ} {ws : List (List ℕ)} {k₀ : ℕ}
    (h : posBind ST ws k₀ = true) : ∀ k < ws.length, ST (k₀ + k) = entL (pos (ws.getD k [])) := by
  induction ws generalizing k₀ with
  | nil => intro k hk; cases hk
  | cons w ws ih =>
    have h' : andB (Nat.beq (ST k₀) (entL (pos w))) (posBind ST ws (Nat.succ k₀)) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    intro k hk
    cases k with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ k =>
      have := ih h2 k (by simpa using hk)
      rw [show k₀ + (k + 1) = Nat.succ k₀ + k by omega, this]
      rfl

theorem pairsOK_spec {blk : ℕ → ℕ} {nf : ℕ} {cs : List (List ℕ)} {XRs : ℕ → ℕ}
    {prs : List (ℕ × List ℕ × ℕ × ℕ × ℕ)} {k₀ : ℕ} (h : pairsOK blk nf cs XRs prs k₀ = true) :
    ∀ k < prs.length, pairOK blk nf cs (XRs (k₀ + k)) (prs.getD k (0, [], 0, 0, 0)) = true := by
  induction prs generalizing k₀ with
  | nil => intro k hk; cases hk
  | cons p prs ih =>
    have h' : andB (pairOK blk nf cs (XRs k₀) p) (pairsOK blk nf cs XRs prs (Nat.succ k₀)) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    intro k hk
    cases k with
    | zero => exact h1
    | succ k =>
      have := ih h2 k (by simpa using hk)
      rw [show k₀ + (k + 1) = Nat.succ k₀ + k by omega]
      exact this

theorem hgOK_spec {blk : ℕ → ℕ} {nf : ℕ} {cs : List (List ℕ)} {hs : List (List ℕ × ℕ × List ℕ × ℕ)}
    (h : hgOK blk nf cs hs = true) : ∀ x ∈ hs, hgOne blk nf cs x = true := by
  induction hs with
  | nil => intro x hx; cases hx
  | cons y hs ih =>
    have h' : andB (hgOne blk nf cs y) (hgOK blk nf cs hs) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact ih h2 x hx

theorem lt6_spec {l : List ℕ} (h : lt6 l = true) : ∀ g ∈ l, g < 6 := by
  induction l with
  | nil => intro g hg; cases hg
  | cons c l ih =>
    have h' : andB (Nat.blt c 6) (lt6 l) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact Nat.le_of_ble_eq_true h1
    · exact ih h2 g hg

theorem csOK_spec {cs : List (List ℕ)} (h : csOK cs = true) : ∀ c ∈ cs, ∀ g ∈ c, g < 6 := by
  induction cs with
  | nil => intro c hc; cases hc
  | cons c cs ih =>
    have h' : andB (lt6 c) (csOK cs) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact lt6_spec h1
    · exact ih h2 d hd

end CertificateChecks.KernelFi22F

end
