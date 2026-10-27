module

public import Certificates.Kernel.F48Small.U42e
public import CFSG.Certificates.Kernel.F48Small.PackSound
import CFSG.Certificates.Kernel.DcKParse

public section

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L

theorem p1W_eq : burnsideF48s_u42eP1W = wordsU42e U42eP1.chars := by
  rw [burnsideF48s_u42eP1W, burnsideF48s_u42eWords, U42eP1.eq, CFSG.KC.DcK.space_eq,
    CFSG.KC.Str.splitOn_ofList, wordsU42e, CFSG.KC.DcK.splitGo_nil, List.map_map]
  congr 1
  funext l
  simp [burnsideF48s_u42eWord]

theorem p2W_eq : burnsideF48s_u42eP2W = wordsU42e U42eP2.chars := by
  rw [burnsideF48s_u42eP2W, burnsideF48s_u42eWords, U42eP2.eq, CFSG.KC.DcK.space_eq,
    CFSG.KC.Str.splitOn_ofList, wordsU42e, CFSG.KC.DcK.splitGo_nil, List.map_map]
  congr 1
  funext l
  simp [burnsideF48s_u42eWord]

theorem letOK_u42e : LetOK 45 5 burnsideF48s_u42eLS burnsideF48s_u42eLSi :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem ek_eq : evK 45 (burnsideF48s_u42eLS.map encL) (burnsideF48s_u42eLSi.map encL) = ekU42e :=
  rfl

theorem ek_eq' (w : List (Fin 5 × Bool)) :
    evK 45 (burnsideF48s_u42eLS.map encL) (burnsideF48s_u42eLSi.map encL) w = ekU42e w :=
  rfl

theorem checkLetters : burnsideF48s_u42eCheckLetters () = true := by
  have e : burnsideF48s_u42eCheckLetters () = lettersTw := by
    simp only [burnsideF48s_u42eCheckLetters, lettersTw, p1W_eq, p2W_eq]
  rw [e]
  exact lettersTw_ok

theorem checkClosed : burnsideF48s_u42eCheckClosed () = true := by
  have h := letOK_u42e
  have e : burnsideF48s_u42eCheckClosed () = closedTw := by
    simp (disch := decide) only [burnsideF48s_u42eCheckClosed, closedTw, burnsideF48s_u42eEvL,
      p1W_eq, p2W_eq, eClosed_ev h, eClosedW_ev h, contains_ev h, List.all_map, Function.comp_def,
      ek_eq, ek_eq', Bool.and_assoc]
  rw [e]
  exact closedTw_ok

theorem checkCand : burnsideF48s_u42eCheckCand () = true := by
  have h := letOK_u42e
  have e : burnsideF48s_u42eCheckCand () = candTw := by
    simp only [burnsideF48s_u42eCheckCand, candTw, burnsideF48s_u42eEvL, p1W_eq, p2W_eq,
      eCandOK_ev h, ek_eq, ek_eq']
  rw [e]
  exact candTw_ok

theorem checkClass : burnsideF48s_u42eCheckClass () = true := by
  have h := letOK_u42e
  have e : burnsideF48s_u42eCheckClass () = classTw := by
    simp only [burnsideF48s_u42eCheckClass, classTw, burnsideF48s_u42eEvL, p1W_eq, p2W_eq,
      List.all_map, List.any_map, Function.comp_def, eNorm_ev h, contains_ev h, Bool.or_assoc,
      Bool.and_assoc,
      contains_compL_ev h, beq_ev h, ek_eq, ek_eq']
  rw [e]
  exact classTw_ok

end CertificateChecks.KernelF48S
