module

public import Certificates.Data.Kernel.SpinOrbK
public import Certificates.Kernel.SpinOrb.Data
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CFSG.KD.SpinOrb

open CFSG.KC.SpinOrb CFSG.KC.Ord

theorem ch13004gam8 : gamRelK 8 16 gam8 = true := by decide +kernel

theorem ch13004gam9 : andB (gamRelK 9 16 gam9) (prefixK 8 gam8 gam9) = true := by decide +kernel

theorem ch13004gam10 : gamRelK 10 32 gam10 = true := by decide +kernel

theorem ch13004gam11 : andB (gamRelK 11 64 gam11) (kronIK 10 32 gam10 gam11) = true := by
  decide +kernel

theorem ch13004words8 : andB (allPairs pairsS8 (wordsOK 8))
    (andB (Nat.beq pairsS8.length 4) (Nat.beq R8.length 4)) = true := by decide +kernel

theorem ch13004words9 : allPairs pairsS8 (wordsOK 9) = true := by decide +kernel

theorem ch13004words10 : andB (allPairs pairsS10 (wordsOK 10))
    (andB (Nat.beq pairsS10.length 5) (Nat.beq R10.length 5)) = true := by decide +kernel

theorem ch13004words11 : allPairs pairsS10 (wordsOK 11) = true := by decide +kernel

#kc_each CFSG.KD.SpinOrb ch13004mat8_ (fun j => matOK 16 gam8 (pairsS8.getD j ([], []))
  (R8.getD j [])) 0 4

#kc_each CFSG.KD.SpinOrb ch13004mat10_ (fun j => matOK 32 gam10 (pairsS10.getD j ([], []))
  (R10.getD j [])) 0 5

#kc_each CFSG.KD.SpinOrb ch13004orb8_ (fun k => orbitK 16 128 R8 T8 S8 TR8 L8 SG8 k) 0 128

#kc_each CFSG.KD.SpinOrb ch13004orb10_ (fun k => orbitK 32 256 R10 T10 S10 TR10 L10 SG10 k) 0 256

theorem ch13004gens : andB (andB (gensEq 8 pairsS8 PG8) (gensEq 9 pairsS8 PG9))
    (andB (gensEq 10 pairsS10 PG10) (gensEq 11 pairsS10 PG11)) = true := by decide +kernel

#kc_each CFSG.KD.SpinOrb ch13004psi8_ (fun k => psiAt 8 64 PG8 PE8 PA8 PS8 PC8 k) 0 64

#kc_each CFSG.KD.SpinOrb ch13004psi9_ (fun k => psiAt 9 64 PG9 PE9 PA9 PS9 PC9 k) 0 64

#kc_each CFSG.KD.SpinOrb ch13004psi10_ (fun k => psiAt 10 128 PG10 PE10 PA10 PS10 PC10 k) 0 128

#kc_each CFSG.KD.SpinOrb ch13004psi11_ (fun k => psiAt 11 128 PG11 PE11 PA11 PS11 PC11 k) 0 128

theorem ch13004abel8 : andB (abelOK 128 4 TR8 L8 A8) (Nat.beq A8.length 8) = true := by
  decide +kernel

#kc_each CFSG.KD.SpinOrb ch13004klein10_ (fun idx => kleinAt 256 L10 KL10 idx) 0 149

#kc_each CFSG.KD.SpinOrb ch13004inv10_ (fun i => invAt 256 L10 INV10 i) 0 256

theorem ch13004invLen10 : Nat.beq INV10.length 59 = true := by decide +kernel

#kc_each CFSG.KD.SpinOrb ch13004pairs10_ (fun a => pairsAt 256 L10 KL10 149 INV10 W10 a) 0 59

end CFSG.KD.SpinOrb
