module

public import Certificates.Kernel.Sporadic.Fi24KPerm.Data
public import CFSG.Certificates.Kernel.Spor.Fi24SevBSound

set_option Elab.async false
set_option maxRecDepth 200000

public section

namespace CFSG.KD.Fi24KPerm.Ck

open CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24ThreeO
  CFSG.KS.Fi24Sev CFSG.KS.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem slcL246 : slcL (nat_lit 246) = true := by decide +kernel

theorem slcP246a : slcP (nat_lit 246) (nat_lit 0) = true := by decide +kernel

theorem slcP246b : slcP (nat_lit 246) (nat_lit 305530) = true := by decide +kernel

theorem slcP246c : slcP (nat_lit 246) (nat_lit 5604) = true := by decide +kernel

theorem slcP246d : slcP (nat_lit 246) (nat_lit 221549) = true := by decide +kernel

theorem slcP246e : slcP (nat_lit 246) (nat_lit 266275) = true := by decide +kernel

theorem slcP246f : slcP (nat_lit 246) (nat_lit 186844) = true := by decide +kernel

theorem slcL247 : slcL (nat_lit 247) = true := by decide +kernel

theorem slcP247a : slcP (nat_lit 247) (nat_lit 0) = true := by decide +kernel

theorem slcP247b : slcP (nat_lit 247) (nat_lit 305530) = true := by decide +kernel

theorem slcP247c : slcP (nat_lit 247) (nat_lit 5604) = true := by decide +kernel

theorem slcP247d : slcP (nat_lit 247) (nat_lit 221549) = true := by decide +kernel

theorem slcP247e : slcP (nat_lit 247) (nat_lit 266275) = true := by decide +kernel

theorem slcP247f : slcP (nat_lit 247) (nat_lit 186844) = true := by decide +kernel

theorem slIn_of {i : ℕ} (hL : slcL i = true) (hP : ∀ b ∈ cb, slcP i b = true) :
    slIn NW NT sl (slQ i) = true := by
  unfold slcL at hL
  have hand : ∀ {a b : Bool}, a = true → b = true → andB a b = true := by
    intro a b ha hb
    subst ha
    subst hb
    rfl
  unfold slIn
  refine allL_of fun e he => ?_
  have h1 := allL_spec hL e he
  refine hand h1 ?_
  unfold agB
  refine allL_of fun b hb => ?_
  have h0 := hP b hb
  unfold slcP at h0
  have h := allL_spec h0 e he
  rwa [ptCB_eq] at h

theorem slPt {i : ℕ} (hi : i = 246 ∨ i = 247) : slIn NW NT sl (slQ i) = true := by
  rcases hi with rfl | rfl
  · refine slIn_of slcL246 fun b hb => ?_
    simp only [cb, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slcP246a
    · exact slcP246b
    · exact slcP246c
    · exact slcP246d
    · exact slcP246e
    · exact slcP246f
  · refine slIn_of slcL247 fun b hb => ?_
    simp only [cb, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slcP247a
    · exact slcP247b
    · exact slcP247c
    · exact slcP247d
    · exact slcP247e
    · exact slcP247f

end CFSG.KD.Fi24KPerm.Ck

end
