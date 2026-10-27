module

public import Certificates.Kernel.F48Small.Sp43c
public import CFSG.Certificates.Kernel.F48Small.Sp43cSound

public section

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L CFSG.KC.Ord CFSG.Quasithin

theorem lt10_B : ∀ w ∈ Sp43cB.codes, ∀ c ∈ w, c < 10 := codesLt10_sound _ codes43c_ok.1
theorem lt10_S : ∀ w ∈ Sp43cS.codes, ∀ c ∈ w, c < 10 := codesLt10_sound _ codes43c_ok.2.1
theorem lt10_P1 : ∀ w ∈ Sp43cP1.codes, ∀ c ∈ w, c < 10 := codesLt10_sound _ codes43c_ok.2.2.1
theorem lt10_P2 : ∀ w ∈ Sp43cP2.codes, ∀ c ∈ w, c < 10 := codesLt10_sound _ codes43c_ok.2.2.2

theorem str_ab : ("ab" : String) = String.ofList ['a', 'b'] := rfl
theorem str_bc : ("bc" : String) = String.ofList ['b', 'c'] := rfl
theorem str_abp : ("abp" : String) = String.ofList ['a', 'b', 'p'] := rfl
theorem str_abq : ("abq" : String) = String.ofList ['a', 'b', 'q'] := rfl

theorem wordB_codes (w : List ℕ) (hw : ∀ c ∈ w, c < 10) :
    burnsideF48s_sp43c_wordB (String.ofList (w.map decSp43c)) = w.map letB43c := by
  simp only [burnsideF48s_sp43c_wordB, burnsideF48s_sp43c_word, String.toList_ofList, List.map_map,
    str_ab]
  apply List.map_congr_left
  intro c hc
  have := hw c hc
  interval_cases c <;> decide

theorem wordS_codes (w : List ℕ) (hw : ∀ c ∈ w, c < 10) :
    burnsideF48s_sp43c_wordS (String.ofList (w.map decSp43c)) = w.map letS43c := by
  simp only [burnsideF48s_sp43c_wordS, burnsideF48s_sp43c_word, String.toList_ofList, List.map_map,
    str_bc]
  apply List.map_congr_left
  intro c hc
  have := hw c hc
  interval_cases c <;> decide

theorem wordP1_codes (w : List ℕ) (hw : ∀ c ∈ w, c < 10) :
    burnsideF48s_sp43c_wordP1 (String.ofList (w.map decSp43c)) = w.map letP43c := by
  simp only [burnsideF48s_sp43c_wordP1, burnsideF48s_sp43c_word, String.toList_ofList, List.map_map,
    str_abp]
  apply List.map_congr_left
  intro c hc
  have := hw c hc
  interval_cases c <;> decide

theorem wordP2_codes (w : List ℕ) (hw : ∀ c ∈ w, c < 10) :
    burnsideF48s_sp43c_wordP2 (String.ofList (w.map decSp43c)) = w.map letQ43c := by
  simp only [burnsideF48s_sp43c_wordP2, burnsideF48s_sp43c_word, String.toList_ofList, List.map_map,
    str_abq]
  apply List.map_congr_left
  intro c hc
  have := hw c hc
  interval_cases c <;> decide

theorem BW_eq : burnsideF48s_sp43c_BW () = wB43c := by
  rw [burnsideF48s_sp43c_BW, Sp43cB.eq, List.map_map, wB43c]
  exact List.map_congr_left fun w hw => wordB_codes w (lt10_B w hw)

theorem SW_eq : burnsideF48s_sp43c_SW () = wS43c := by
  rw [burnsideF48s_sp43c_SW, Sp43cS.eq, List.map_map, wS43c]
  exact List.map_congr_left fun w hw => wordS_codes w (lt10_S w hw)

theorem P1W_eq : burnsideF48s_sp43c_P1W () = wP143c := by
  rw [burnsideF48s_sp43c_P1W, Sp43cP1.eq, List.map_map, wP143c]
  exact List.map_congr_left fun w hw => wordP1_codes w (lt10_P1 w hw)

theorem P2W_eq : burnsideF48s_sp43c_P2W () = wP243c := by
  rw [burnsideF48s_sp43c_P2W, Sp43cP2.eq, List.map_map, wP243c]
  exact List.map_congr_left fun w hw => wordP2_codes w (lt10_P2 w hw)

theorem Bw_getD (i : ℕ) :
    burnsideF48s_sp43c_wordB (burnsideF48s_sp43c_Bw.getD i "") = wB43c.getD i [] := by
  have hd : ("" : String) = String.ofList (([] : List ℕ).map decSp43c) := rfl
  rw [Sp43cB.eq, hd, List.getD_map, wB43c, ← List.map_nil (f := letB43c), List.getD_map]
  exact wordB_codes _ (lt10_getD codes43c_ok.1 i)

theorem letOK2 : LetOK 45 2 burnsideF48s_sp43c_LS burnsideF48s_sp43c_LSi :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem letOK3 : LetOK 45 3 burnsideF48s_sp43c_LS burnsideF48s_sp43c_LSi :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem letOK4 : LetOK 45 4 burnsideF48s_sp43c_LS burnsideF48s_sp43c_LSi :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem letOKS : LetOK 45 2 sLS43c sLSi43c :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem letOKQ : LetOK 45 3 qLS43c qLSi43c :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem valL (k : ℕ) (hk : k < 4) : Val 45 (burnsideF48s_sp43c_L k) := by
  have hl : burnsideF48s_sp43c_LS.length = 4 := by decide
  refine val_of_letOK letOK4 (List.mem_append_left _ ?_)
  rw [burnsideF48s_sp43c_L, List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem valLi (k : ℕ) (hk : k < 4) : Val 45 (burnsideF48s_sp43c_Li k) := by
  have hl : burnsideF48s_sp43c_LSi.length = 4 := by decide
  refine val_of_letOK letOK4 (List.mem_append_right _ ?_)
  rw [burnsideF48s_sp43c_Li, List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem evL_B : burnsideF48s_sp43c_evL burnsideF48s_sp43c_glB burnsideF48s_sp43c_gliB =
    burnsideF48s_eEvL 45 burnsideF48s_sp43c_LS burnsideF48s_sp43c_LSi :=
  evL_eq _ _ _ _ (fun _ => rfl) (fun _ => rfl)

theorem evL_P1 : burnsideF48s_sp43c_evL burnsideF48s_sp43c_glP1 burnsideF48s_sp43c_gliP1 =
    burnsideF48s_eEvL 45 burnsideF48s_sp43c_LS burnsideF48s_sp43c_LSi :=
  evL_eq _ _ _ _ (fun _ => rfl) (fun _ => rfl)

theorem evL_4 : burnsideF48s_sp43c_evL burnsideF48s_sp43c_gl4 burnsideF48s_sp43c_gli4 =
    burnsideF48s_eEvL 45 burnsideF48s_sp43c_LS burnsideF48s_sp43c_LSi :=
  evL_eq _ _ _ _ (fun _ => rfl) (fun _ => rfl)

theorem glS_eq (k : Fin 2) : burnsideF48s_sp43c_glS k = sLS43c.getD k [] := by
  fin_cases k <;> rfl

theorem gliS_eq (k : Fin 2) : burnsideF48s_sp43c_gliS k = sLSi43c.getD k [] := by
  fin_cases k <;> rfl

theorem glP2_eq (k : Fin 3) : burnsideF48s_sp43c_glP2 k = qLS43c.getD k [] := by
  fin_cases k <;> rfl

theorem gliP2_eq (k : Fin 3) : burnsideF48s_sp43c_gliP2 k = qLSi43c.getD k [] := by
  fin_cases k <;> rfl

theorem evL_S : burnsideF48s_sp43c_evL burnsideF48s_sp43c_glS burnsideF48s_sp43c_gliS =
    burnsideF48s_eEvL 45 sLS43c sLSi43c :=
  evL_eq _ _ _ _ glS_eq gliS_eq

theorem evL_P2 : burnsideF48s_sp43c_evL burnsideF48s_sp43c_glP2 burnsideF48s_sp43c_gliP2 =
    burnsideF48s_eEvL 45 qLS43c qLSi43c :=
  evL_eq _ _ _ _ glP2_eq gliP2_eq

theorem sp43c_checkSub : burnsideF48s_sp43c_checkSub () = true := by
  obtain ⟨⟨hB1, hB2⟩, ⟨hS1, hS2⟩, ⟨hP1, hP1'⟩, ⟨hQ1, hQ2⟩⟩ := shape43c_ok
  simp only [burnsideF48s_sp43c_checkSub, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [BW_eq]
    exact groupB_of letOK2 (fun _ => rfl) (fun _ => rfl) hB1 hB2 (by decide) subB43c_ok
  · rw [SW_eq]
    exact groupB_of letOKS glS_eq gliS_eq hS1 hS2 (by decide) subS43c_ok
  · rw [P1W_eq]
    exact groupB_of letOK3 (fun _ => rfl) (fun _ => rfl) hP1 hP1' (by decide) subP143c_ok
  · rw [P2W_eq]
    exact groupB_of letOKQ glP2_eq gliP2_eq hQ1 hQ2 (by decide) subP243c_ok

theorem encL_Bl (i : ℕ) : encL (burnsideF48s_sp43c_Bl i) = bK43c i := by
  rw [burnsideF48s_sp43c_Bl, Bw_getD, evL_B, encL_ev letOK2, bK43c]

theorem valBl (i : ℕ) : Val 45 (burnsideF48s_sp43c_Bl i) := by
  rw [burnsideF48s_sp43c_Bl, Bw_getD, evL_B]
  exact val_ev letOK2 _

theorem encL_Dl (j : ℕ) : encL (burnsideF48s_sp43c_Dl j) = dK43c j := by
  rw [burnsideF48s_sp43c_Dl, burnsideF48s_sp43c_evL4, evL_4, encL_ev letOK4, dK43c]

theorem valDl (j : ℕ) : Val 45 (burnsideF48s_sp43c_Dl j) := by
  rw [burnsideF48s_sp43c_Dl, burnsideF48s_sp43c_evL4, evL_4]
  exact val_ev letOK4 _

theorem coverB_eq (s : ℕ) (hs : s < 4) (tr : List ℕ) (wit : List (ℕ × ℕ))
    (dec : List (List (ℕ × ℕ × ℕ))) :
    burnsideF48s_sp43c_coverB s tr wit dec = coverK43c s tr wit dec := by
  have hL := valL s hs
  simp (disch := repeat (first | assumption | apply val_compL45 | exact valBl _ | exact valDl _))
    only [burnsideF48s_sp43c_coverB, coverK43c, decide_eq_encL, encL_compL45, encL_Bl, encL_Dl]

theorem sp43c_checkCover : burnsideF48s_sp43c_checkCover () = true := by
  rw [burnsideF48s_sp43c_checkCover, coverB_eq 2 (by decide), coverB_eq 3 (by decide),
    cover43c_ok.1, cover43c_ok.2, Bool.and_self]

theorem sp43c_checkS : burnsideF48s_sp43c_checkS () = true := by
  have e : burnsideF48s_sp43c_checkS () = checkSK43c sT43c := by
    simp (disch := repeat (first | apply val_compL45 | exact valL _ (by decide) |
        exact valLi _ (by decide) | exact val_ev letOKS _))
      only [burnsideF48s_sp43c_checkS, checkSK43c, sT43c, burnsideF48s_sp43c_SL, SW_eq, evL_S,
        List.all_map, Function.comp_def, List.all_cons, List.all_nil, Bool.and_true,
        contains_val letOKS, encL_compL45, encL_ev letOKS]
  rw [e]
  exact s43c_ok

theorem sp43c_checkNot : burnsideF48s_sp43c_checkNot () = true := by
  have e : burnsideF48s_sp43c_checkNot () =
      (!memT (setT (wP243c.map (evK 45 (qLS43c.map encL) (qLSi43c.map encL))))
        (encL (burnsideF48s_sp43c_L 2)) &&
      !memT (setT (wP143c.map
        (evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL))))
        (encL (burnsideF48s_sp43c_L 3))) := by
    simp (disch := exact valL _ (by decide))
      only [burnsideF48s_sp43c_checkNot, burnsideF48s_sp43c_P1L, burnsideF48s_sp43c_P2L, P1W_eq,
        P2W_eq, evL_P1, evL_P2, contains_val letOK3, contains_val letOKQ]
  rw [e]
  exact not43c_ok

end CertificateChecks.KernelF48S
