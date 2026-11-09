module

public import Certificates.Kernel.Sporadic.Fi7Perm.Data
public import CFSG.Certificates.Kernel.Spor.Fi24SevBSound

set_option Elab.async false

public section

namespace CFSG.KD.Fi7Perm.Ck

open CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24ThreeO
  CFSG.KS.Fi24Sev CFSG.KS.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem slcL180 : slcL (nat_lit 180) = true := by decide +kernel

theorem slcP180a : slcP (nat_lit 180) (nat_lit 0) = true := by decide +kernel

theorem slcP180b : slcP (nat_lit 180) (nat_lit 305530) = true := by decide +kernel

theorem slcP180c : slcP (nat_lit 180) (nat_lit 5604) = true := by decide +kernel

theorem slcP180d : slcP (nat_lit 180) (nat_lit 221549) = true := by decide +kernel

theorem slcP180e : slcP (nat_lit 180) (nat_lit 266275) = true := by decide +kernel

theorem slcP180f : slcP (nat_lit 180) (nat_lit 186844) = true := by decide +kernel

theorem sl180 : slIn NW NT sl (slQ 180) = true := by
  have hL := slcL180
  unfold slcL at hL
  have hP : ∀ b ∈ cb, slcP 180 b = true := by
    intro b hb
    simp only [cb, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slcP180a
    · exact slcP180b
    · exact slcP180c
    · exact slcP180d
    · exact slcP180e
    · exact slcP180f
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

end CFSG.KD.Fi7Perm.Ck

end
