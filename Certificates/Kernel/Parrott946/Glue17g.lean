
module

public import Certificates.Kernel.Parrott946.Glue17f

set_option maxRecDepth 400000
set_option exponentiation.threshold 300

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup
  CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

theorem nodup_of_f2 {LP : List ℕ} {L : List P45} (hF : List.Forall₂ (PRep 45 6) LP L)
    (hn : LP.Nodup) (hlt : ∀ P ∈ LP, P < 2 ^ 270) : L.Nodup := by
  induction hF with
  | nil => exact List.nodup_nil
  | @cons P x LP L hPx hF ih =>
    rw [List.nodup_cons] at hn ⊢
    refine ⟨fun hx => ?_, ih hn.2 fun Q hQ => hlt Q (List.mem_cons_of_mem _ hQ)⟩
    obtain ⟨Q, hQ, hQx⟩ := f2_mem_right hF hx
    have e : P = Q :=
      prep_canon_eq hPx hQx (hlt P List.mem_cons_self) (hlt Q (List.mem_cons_of_mem _ hQ))
    apply hn.1
    rw [e]
    exact hQ

theorem inv_mem_of_mul {L : List P45} (h1 : (1 : P45) ∈ L)
    (hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) {x : P45} (hx : x ∈ L) : x⁻¹ ∈ L := by
  have hpow : ∀ k : ℕ, x ^ k ∈ L := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ ih _ hx
  have hn := orderOf_pos x
  have e : x * x ^ (orderOf x - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [inv_eq_of_mul_eq_one_right e]
  exact hpow _

theorem list_facts {LP : List ℕ} {L gs : List P45}
    (hF : List.Forall₂ (PRep 45 6) LP L) (hmc : mulClosedK 45 6 LP = true)
    (hd : distinctK LP = true) (hlt : ∀ P ∈ LP, P < 2 ^ 270) (h1 : (1 : P45) ∈ L)
    (hg : ∀ g ∈ gs, g ∈ L) (hA : ∀ x ∈ L, x ∈ A) : ListGroupFacts L gs := by
  have hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L := by
    intro x hx y hy
    obtain ⟨Px, hPx, hx'⟩ := f2_mem_right hF hx
    obtain ⟨Py, hPy, hy'⟩ := f2_mem_right hF hy
    obtain ⟨z, hz, hz'⟩ := f2_mem_left hF (mulClosedK_spec hmc hPx hPy)
    rw [prep_eq (prep_pc hx' hy') hz']
    exact hz
  exact
    { nodup := nodup_of_f2 hF (distinctK_spec hd) hlt
      one_mem := h1
      mul_closed := List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy =>
        decide_eq_true (hmul x hx y hy)
      inv_closed := List.all_eq_true.2 fun x hx => decide_eq_true (inv_mem_of_mul h1 hmul hx)
      gens_mem := List.all_eq_true.2 fun g hg' => decide_eq_true (hg g hg')
      in_A := List.all_eq_true.2 fun x hx => (mem_iff_sift QA45 QA45_ok x).1 (hA x hx) }

theorem entry_rec {LP : List ℕ} {L : List P45} (hF : List.Forall₂ (PRep 45 6) LP L) {j : ℕ}
    (hj : j < LP.length) : ∃ y ∈ L, PRep 45 6 (LP.getD j 0) y :=
  f2_mem_left hF (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)

theorem Q8list_eq : Q8list () = [1, alpha2, alpha2 * alpha2, alpha2 * alpha2 * alpha2, beta2,
    beta2 * alpha2, beta2 * (alpha2 * alpha2), beta2 * (alpha2 * alpha2 * alpha2)] := by
  simp only [Q8list, tabList_eq, tab_eq]

theorem q8_group : ListGroupFacts (Q8list ()) Q8gens := by
  have h := c17_q8
  simp only [q8K, strictB_eq', Bool.and_eq_true] at h
  have ha2 := prep_pc prep_a2 prep_a2
  have ha3 := prep_pc ha2 prep_a2
  rw [Q8list_eq]
  refine list_facts (.cons prep_pid (.cons prep_a2 (.cons ha2 (.cons ha3 (.cons prep_b2
    (.cons (prep_pc prep_b2 prep_a2) (.cons (prep_pc prep_b2 ha2) (.cons (prep_pc prep_b2 ha3)
    .nil)))))))) h.1 h.2 ?_ List.mem_cons_self ?_ ?_
  · intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pidn_lt (by norm_num) (by norm_num)
    · exact lane_lt 270 _ _
    · exact pcomp_lt (by norm_num)
    · exact pcomp_lt (by norm_num)
    · exact lane_lt 270 _ _
    · exact pcomp_lt (by norm_num)
    · exact pcomp_lt (by norm_num)
    · exact pcomp_lt (by norm_num)
  · intro g hg
    simp only [Q8gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · simp
  · intro x hx
    have a := alpha2_memA
    have b := beta2_memA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact a
    · exact A.mul_mem a a
    · exact A.mul_mem (A.mul_mem a a) a
    · exact b
    · exact A.mul_mem b a
    · exact A.mul_mem b (A.mul_mem a a)
    · exact A.mul_mem b (A.mul_mem (A.mul_mem a a) a)

theorem D8list_eq : D8list () = [1, t * (v * beta), t * (v * beta) * (t * (v * beta)),
    t * (v * beta) * (t * (v * beta)) * (t * (v * beta)), t, t * (t * (v * beta)),
    t * (t * (v * beta) * (t * (v * beta))),
    t * (t * (v * beta) * (t * (v * beta)) * (t * (v * beta)))] := by
  simp only [D8list, tabList_eq, tab_eq]

theorem prep_r : PRep 45 6 (pc (wE 0) (pc (wE 2) (wE 9))) (t * (v * beta)) :=
  prep_pc prep_t (prep_pc prep_v prep_beta)

theorem d8_f2 : List.Forall₂ (PRep 45 6)
    [pidn 45 6, pc (wE 0) (pc (wE 2) (wE 9)),
      pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9))),
      pc (pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9))))
        (pc (wE 0) (pc (wE 2) (wE 9))), wE 0, pc (wE 0) (pc (wE 0) (pc (wE 2) (wE 9))),
      pc (wE 0) (pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9)))),
      pc (wE 0) (pc (pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9))))
        (pc (wE 0) (pc (wE 2) (wE 9))))]
    (D8list ()) := by
  have r2 := prep_pc prep_r prep_r
  have r3 := prep_pc r2 prep_r
  rw [D8list_eq]
  exact .cons prep_pid (.cons prep_r (.cons r2 (.cons r3 (.cons prep_t (.cons (prep_pc prep_t prep_r)
    (.cons (prep_pc prep_t r2) (.cons (prep_pc prep_t r3) .nil)))))))

theorem d8_lt : ∀ P ∈ [pidn 45 6, pc (wE 0) (pc (wE 2) (wE 9)),
      pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9))),
      pc (pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9))))
        (pc (wE 0) (pc (wE 2) (wE 9))), wE 0, pc (wE 0) (pc (wE 0) (pc (wE 2) (wE 9))),
      pc (wE 0) (pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9)))),
      pc (wE 0) (pc (pc (pc (wE 0) (pc (wE 2) (wE 9))) (pc (wE 0) (pc (wE 2) (wE 9))))
        (pc (wE 0) (pc (wE 2) (wE 9))))], P < 2 ^ 270 := by
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pidn_lt (by norm_num) (by norm_num)
  · exact pcomp_lt (by norm_num)
  · exact pcomp_lt (by norm_num)
  · exact pcomp_lt (by norm_num)
  · exact lane_lt 270 _ _
  · exact pcomp_lt (by norm_num)
  · exact pcomp_lt (by norm_num)
  · exact pcomp_lt (by norm_num)

theorem d8_mem_of_any {L : List ℕ} {Q : ℕ} {x : P45} (hF : List.Forall₂ (PRep 45 6) L (D8list ()))
    (h : anyL L (fun _ y => Nat.beq y Q) 0 = true) (hx : PRep 45 6 Q x) : x ∈ D8list () := by
  obtain ⟨j, hj, e⟩ := anyL_spec h
  obtain ⟨y, hy, hpy⟩ := entry_rec hF hj
  rw [Nat.eq_of_beq_eq_true e] at hpy
  rw [prep_eq hx hpy]
  exact hy

theorem d8_group : ListGroupFacts (D8list ()) D8gens := by
  have h := c17_d8
  simp only [d8K, strictB_eq', Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hmc, hd⟩, hu⟩, hvb⟩, -⟩ := h
  refine list_facts d8_f2 hmc hd d8_lt (by rw [D8list_eq]; exact List.mem_cons_self) ?_ ?_
  · intro g hg
    simp only [D8gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · rw [D8list_eq]
      simp
    · exact d8_mem_of_any d8_f2 hu prep_u
    · exact d8_mem_of_any d8_f2 hvb (prep_pc prep_v prep_beta)
  · intro x hx
    have ht := t_memA
    have hr : t * (v * beta) ∈ A := A.mul_mem ht (A.mul_mem v_memA beta_memA)
    rw [D8list_eq] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact hr
    · exact A.mul_mem hr hr
    · exact A.mul_mem (A.mul_mem hr hr) hr
    · exact ht
    · exact A.mul_mem ht hr
    · exact A.mul_mem ht (A.mul_mem hr hr)
    · exact A.mul_mem ht (A.mul_mem (A.mul_mem hr hr) hr)

theorem d8_center : d8CenterCheck () = true := by
  have h := c17_d8
  simp only [d8K, strictB_eq', Bool.and_eq_true] at h
  obtain ⟨-, hc⟩ := h
  have hvb := prep_pc prep_v prep_beta
  unfold d8CenterCheck
  simp only [tabList_eq, tab_eq, D8gens]
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨P, hP, hPx⟩ := f2_mem_right d8_f2 hx
  obtain ⟨j, hj, hPj⟩ := List.mem_iff_getElem.1 hP
  have hc' := allL_spec hc j hj
  rw [List.getD_eq_getElem _ _ hj, hPj] at hc'
  rw [Bool.or_eq_true, Bool.or_eq_true]
  by_cases hcm : x * t = t * x ∧ x * u = u * x ∧ x * (v * beta) = v * beta * x
  · obtain ⟨c1, c2, c3⟩ := hcm
    have e1 : cmm P (wE 0) = true := eq22_of_mul17 hPx prep_t prep_t hPx c1
    have e2 : cmm P (wE 1) = true := eq22_of_mul17 hPx prep_u prep_u hPx c2
    have e3 : cmm P (pc (wE 2) (wE 9)) = true := eq22_of_mul17 hPx hvb hvb hPx c3
    rw [e1, e2, e3] at hc'
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hc'
    rcases hc' with h | h
    · exact Or.inl (Or.inr (decide_eq_true (eq_of_eqP h hPx prep_pid)))
    · have e := Nat.eq_of_beq_eq_true h
      rw [e] at hPx
      exact Or.inr (decide_eq_true (prep_eq hPx prep_ut))
  · refine Or.inl (Or.inl ?_)
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hall
    apply hcm
    have h3 := List.all_eq_true.1 hall
    exact ⟨of_decide_eq_true (h3 t (by simp)), of_decide_eq_true (h3 u (by simp)),
      of_decide_eq_true (h3 (v * beta) (by simp))⟩

end CertificateChecks.Parrott946

end
