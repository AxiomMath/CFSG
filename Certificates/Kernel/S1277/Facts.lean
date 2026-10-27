module

public import Certificates.Kernel.S1277.SvFacts
public import Certificates.Kernel.S1277.Link
public import Certificates.Kernel.S1277.Cand
public import Certificates.Kernel.S1277.Arith

public section

namespace CFSG.KP.S1277Facts

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Cand CFSG.KD.S1277Mod CFSG.KD.S1277Lat
  CFSG.KD.S1277Cand CFSG.KD.S1277Fr CFSG.KD.S1277Sig CFSG.KD.S1277Ar CFSG.KS.S1277Lat
  CFSG.KS.S1277Cand CFSG.KS.S1277Ar CFSG.KS.S1277Facts CFSG.KP.S1277Lat CFSG.KP.S1277Cand
  CFSG.KP.S1277Link CFSG.KP.S1277Mod CFSG.KP.S1277Fr CFSG.KP.S1277Sig CFSG.KP.S1277Ar
  CFSG.Quasithin.H13.S127.Mod CFSG.Quasithin.H13.I1277 Certificates.Data.S1277Struct
  Certificates.Data.S1277Facts

theorem getD_of_mem {l : List ℕ} {i : ℕ} (h : i ∈ l) : ∃ j < l.length, l.getD j 0 = i := by
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem h
  exact ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj, hji]⟩

theorem nfig_eq : nfig = [] := by decide +kernel

theorem len_g : nmg.length = 23 ∧ svg = 23 ∧ olg < nmg.length := by decide +kernel

theorem len_n : oln < nmn.length := by decide +kernel

theorem modelFacts_gm6 : ModelFacts1277 gm6 := by
  refine ⟨modFacts_gm6.nodup, ?_⟩
  intro G _ _ H K Q κ z hκ' hKH hQK hQn hQ2 _ _ hzH hzK hzc
  have hκ := mcod_g hκ'
  rw [zc_g] at hzc
  have hQnK : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := fun k hk => hQn k (hKH hk)
  obtain ⟨i, hi, hQN⟩ := normal_two_eq_node hκ gen_g nodes_g cls_g ox_g join_g bot_g quot_g hQK
    hQnK hQ2
  have hN := nodesChk_spec nodes_g i hi
  rcases cov_sound cov_g i hi with h | h | h | h
  · obtain ⟨j, hj, rfl⟩ := getD_of_mem h
    have hc := ncAll_spec nc_g j hj
    rw [← hzc] at hc
    refine Or.inr (Or.inr (Or.inl ?_))
    unfold NCFacts
    exact nc_sound hκ hN hQK hQN hc
  · obtain ⟨j, hj, rfl⟩ := getD_of_mem h
    obtain ⟨hV, hbp, hlt, hlen, hfix, hpair⟩ := v_sound hκ hN hQK hQN (vAll_spec v_g j hj)
    refine Or.inl ?_
    unfold VFacts
    refine ⟨fun c hc => by rw [modFacts_gm6.idB]; exact hV c hc, _, hbp,
      fun i hi => by rw [modFacts_gm6.length]; exact hlt i hi, census_G0 modFacts_gm6 hlt hlen hfix
        hpair⟩
  · rw [nfig_eq] at h
    exact absurd h List.not_mem_nil
  · obtain ⟨j, hj, rfl⟩ := getD_of_mem h
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    have hfr := fr_g
    rw [← hzc] at hfr
    exact sigFacts_of_tables hQK hQn hκ hzH hzK gen_g nodes_g hfr sig_ok ar_g x_ok len_g.2.2 hj
      hi (by rw [len_g.2.1, ← len_g.1]; exact Nat.ne_of_lt hi) hQN

theorem modelFacts_nm6 : ModelFacts1277 nm6 := by
  refine ⟨modFacts_nm6.nodup, ?_⟩
  intro G _ _ H K Q κ z hκ' hKH hQK hQn hQ2 _ _ hzH hzK hzc
  have hκ := mcod_n hκ'
  rw [zc_n] at hzc
  have hQnK : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := fun k hk => hQn k (hKH hk)
  obtain ⟨i, hi, hQN⟩ := normal_two_eq_node hκ gen_n nodes_n cls_n ox_n join_n bot_n quot_n hQK
    hQnK hQ2
  have hN := nodesChk_spec nodes_n i hi
  rcases cov_sound cov_n i hi with h | h | h | h
  · obtain ⟨j, hj, rfl⟩ := getD_of_mem h
    have hc := ncAll_spec nc_n j hj
    rw [← hzc] at hc
    refine Or.inr (Or.inr (Or.inl ?_))
    unfold NCFacts
    exact nc_sound hκ hN hQK hQN hc
  · obtain ⟨j, hj, rfl⟩ := getD_of_mem h
    obtain ⟨hV, hbp, hlt, hlen, hfix, hpair⟩ := v_sound hκ hN hQK hQN (vAll_spec v_n j hj)
    refine Or.inl ?_
    unfold VFacts
    refine ⟨fun c hc => by rw [modFacts_nm6.idB]; exact hV c hc, _, hbp,
      fun i hi => by rw [modFacts_nm6.length]; exact hlt i hi, census_G0 modFacts_nm6 hlt hlen hfix
        hpair⟩
  · obtain ⟨j, hj, rfl⟩ := getD_of_mem h
    refine Or.inr (Or.inl ?_)
    unfold NFFacts
    exact nf_sound hκ hN hQK hQN (nfAll_spec nf_n j hj)
  · obtain ⟨j, hj, rfl⟩ := getD_of_mem h
    by_cases hsv : sgin.getD j 0 = svn
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      rw [hsv, svn_eq] at hQN
      exact CFSG.KP.S1277Sv.survFacts_n hKH hQK hQn hκ hzH hzK hzc hQN
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      have hfr := fr_n
      rw [← hzc] at hfr
      exact sigFacts_of_tables hQK hQn hκ hzH hzK gen_n nodes_n hfr sig_ok ar_n x_ok len_n hj hi
        hsv hQN

end CFSG.KP.S1277Facts

end
