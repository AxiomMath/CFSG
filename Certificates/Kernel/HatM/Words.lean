module

public import Certificates.Kernel.HatM.Data
public import Certificates.Data.Kernel.Spor.Raw
import Certificates.Kernel.Sporadic.StrList
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHatM

open CFSG.Quasithin.H13.Ch4.HatM
open CFSG.KC.Enum (pidn)
open CFSG.KS (mask)
open CFSG.KS.Raw (wordK lettersK)

@[expose] def letterCode (ch : Char) : ℤ := if ch = 'a' then 1 else if ch = 'b' then 2 else -2

@[expose] noncomputable def wordOK (cs : List Char) (P : ℕ) : Bool :=
  lettersK 2 (cs.map letterCode) &&
    Nat.beq (wordK 24 5 (mask 5) (pidn 24 5) AB ABI (cs.map letterCode)) P

theorem wS1 : (List.range 9).all
    (fun k => wordOK ((s1WordStrs.map String.toList).getD k []) (ES1.G k)) = true := by
  simp only [s1WordStrs, List.map_cons, List.map_nil, String.toList_append, strToList]
  quickRfl

theorem wP1 : (List.range 10).all
    (fun k => wordOK ((p1WordStrs.map String.toList).getD k []) (EP1.G k)) = true := by
  simp only [p1WordStrs, List.map_cons, List.map_nil, String.toList_append, strToList]
  quickRfl

theorem wC : wordOK cWordStr.toList (RA 2) = true := by
  simp only [cWordStr, String.toList_append, strToList]
  quickRfl

end CertificateChecks.KernelHatM

end
