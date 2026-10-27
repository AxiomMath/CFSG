module

public import Certificates.Kernel.F48Small.Sp43
public import Certificates.Kernel.F48Small.Sp43e
public import CFSG.Certificates.Kernel.F48Small.PackSound
import CFSG.Certificates.Kernel.DcKParse

public section

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L

theorem sp43P1W_eq : burnsideF48s_sp43P1W = wordsSp43 Sp43P1.chars := by
  rw [burnsideF48s_sp43P1W, burnsideF48s_sp43Words, Sp43P1.eq, CFSG.KC.DcK.space_eq,
    CFSG.KC.Str.splitOn_ofList, wordsSp43, CFSG.KC.DcK.splitGo_nil, List.map_map]
  congr 1
  funext l
  simp [burnsideF48s_sp43Word]

theorem sp43P2W_eq : burnsideF48s_sp43P2W = wordsSp43 Sp43P2.chars := by
  rw [burnsideF48s_sp43P2W, burnsideF48s_sp43Words, Sp43P2.eq, CFSG.KC.DcK.space_eq,
    CFSG.KC.Str.splitOn_ofList, wordsSp43, CFSG.KC.DcK.splitGo_nil, List.map_map]
  congr 1
  funext l
  simp [burnsideF48s_sp43Word]

theorem letOK_sp43 : LetOK 45 4 burnsideF48s_sp43LS burnsideF48s_sp43LSi :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem ekSp43_eq : evK 45 (burnsideF48s_sp43LS.map encL) (burnsideF48s_sp43LSi.map encL) = ekSp43 :=
  rfl

theorem ekSp43_eq' (w : List (Fin 4 × Bool)) :
    evK 45 (burnsideF48s_sp43LS.map encL) (burnsideF48s_sp43LSi.map encL) w = ekSp43 w :=
  rfl

theorem sp43_checkLetters : burnsideF48s_sp43CheckLetters () = true := by
  have e : burnsideF48s_sp43CheckLetters () = lettersSp43 := by
    simp only [burnsideF48s_sp43CheckLetters, lettersSp43, sp43P1W_eq, sp43P2W_eq]
  rw [e]
  exact lettersSp43_ok

theorem sp43_checkClosed : burnsideF48s_sp43CheckClosed () = true := by
  have h := letOK_sp43
  have e : burnsideF48s_sp43CheckClosed () = closedSp43 := by
    simp (disch := decide) only [burnsideF48s_sp43CheckClosed, closedSp43, burnsideF48s_sp43EvL,
      sp43P1W_eq, sp43P2W_eq, eClosed_ev h, ekSp43_eq, ekSp43_eq', Bool.and_assoc]
  rw [e]
  exact closedSp43_ok

theorem sp43_checkCand : burnsideF48s_sp43CheckCand () = true := by
  have h := letOK_sp43
  have e : burnsideF48s_sp43CheckCand () = candSp43 := by
    simp only [burnsideF48s_sp43CheckCand, candSp43, burnsideF48s_sp43EvL, sp43P1W_eq, sp43P2W_eq,
      eCandOK_ev h, ekSp43_eq, ekSp43_eq']
  rw [e]
  exact candSp43_ok

theorem sp43eP1W_eq : burnsideF48s_sp43eP1W = wordsSp43e Sp43eP1.chars := by
  rw [burnsideF48s_sp43eP1W, burnsideF48s_sp43eWords, Sp43eP1.eq, CFSG.KC.DcK.space_eq,
    CFSG.KC.Str.splitOn_ofList, wordsSp43e, CFSG.KC.DcK.splitGo_nil, List.map_map]
  congr 1
  funext l
  simp [burnsideF48s_sp43eWord]

theorem sp43eP2W_eq : burnsideF48s_sp43eP2W = wordsSp43e Sp43eP2.chars := by
  rw [burnsideF48s_sp43eP2W, burnsideF48s_sp43eWords, Sp43eP2.eq, CFSG.KC.DcK.space_eq,
    CFSG.KC.Str.splitOn_ofList, wordsSp43e, CFSG.KC.DcK.splitGo_nil, List.map_map]
  congr 1
  funext l
  simp [burnsideF48s_sp43eWord]

theorem letOK_sp43e : LetOK 45 5 burnsideF48s_sp43eLS burnsideF48s_sp43eLSi :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem ekSp43e_eq :
    evK 45 (burnsideF48s_sp43eLS.map encL) (burnsideF48s_sp43eLSi.map encL) = ekSp43e :=
  rfl

theorem ekSp43e_eq' (w : List (Fin 5 × Bool)) :
    evK 45 (burnsideF48s_sp43eLS.map encL) (burnsideF48s_sp43eLSi.map encL) w = ekSp43e w :=
  rfl

theorem sp43e_checkLetters : burnsideF48s_sp43eCheckLetters () = true := by
  have e : burnsideF48s_sp43eCheckLetters () = lettersSp43e := by
    simp only [burnsideF48s_sp43eCheckLetters, lettersSp43e, sp43eP1W_eq, sp43eP2W_eq]
  rw [e]
  exact lettersSp43e_ok

theorem sp43e_checkClosed : burnsideF48s_sp43eCheckClosed () = true := by
  have h := letOK_sp43e
  have e : burnsideF48s_sp43eCheckClosed () = closedSp43e := by
    simp (disch := decide) only [burnsideF48s_sp43eCheckClosed, closedSp43e, burnsideF48s_sp43eEvL,
      sp43eP1W_eq, sp43eP2W_eq, eClosed_ev h, eClosedW_ev h, ekSp43e_eq, ekSp43e_eq', Bool.and_assoc]
  rw [e]
  exact closedSp43e_ok

theorem sp43e_checkCand : burnsideF48s_sp43eCheckCand () = true := by
  have h := letOK_sp43e
  have e : burnsideF48s_sp43eCheckCand () = candSp43e := by
    simp only [burnsideF48s_sp43eCheckCand, candSp43e, burnsideF48s_sp43eEvL, sp43eP1W_eq,
      sp43eP2W_eq, eCandOK_ev h, ekSp43e_eq, ekSp43e_eq']
  rw [e]
  exact candSp43e_ok

end CertificateChecks.KernelF48S
