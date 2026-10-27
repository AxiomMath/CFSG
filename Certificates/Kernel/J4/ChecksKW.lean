module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

theorem kw0 : Nat.beq (runK kd KW0 (mkC (nat_lit 0) (nat_lit 1))) (nat_lit 8589934742) = true := by quickRfl

theorem kw1 : Nat.beq (runK kd KW1 (nat_lit 8589934742)) (nat_lit 8589934892) = true := by quickRfl

theorem kw2 : Nat.beq (runK kd KW2 (nat_lit 8589934892)) (nat_lit 8589935042) = true := by quickRfl

theorem kw3 : Nat.beq (runK kd KW3 (nat_lit 8589935042)) (nat_lit 12884902488) = true := by quickRfl

theorem kw4 : Nat.beq (runK kd KW4 (nat_lit 12884902488)) (nat_lit 12884902638) = true := by quickRfl

theorem kw5 : Nat.beq (runK kd KW5 (nat_lit 12884902638)) (nat_lit 12884902788) = true := by quickRfl

theorem kw6 : Nat.beq (runK kd KW6 (nat_lit 12884902788)) (nat_lit 17179870234) = true := by quickRfl

theorem kw7 : Nat.beq (runK kd KW7 (nat_lit 17179870234)) (nat_lit 17179870384) = true := by quickRfl

theorem kw8 : Nat.beq (runK kd KW8 (nat_lit 17179870384)) (nat_lit 21474837830) = true := by quickRfl

theorem kw9 : Nat.beq (runK kd KW9 (nat_lit 21474837830)) (nat_lit 21474837980) = true := by quickRfl

theorem kw10 : Nat.beq (runK kd KW10 (nat_lit 21474837980)) (nat_lit 25769805426) = true := by quickRfl

theorem kw11 : Nat.beq (runK kd KW11 (nat_lit 25769805426)) (mkC kd.NF kd.ND) = true := by quickRfl

theorem mt0 : Nat.beq (runT md kd MT0 (nat_lit 0)) (nat_lit 10) = true := by quickRfl

theorem mt1 : Nat.beq (runT md kd MT1 (nat_lit 10)) (nat_lit 20) = true := by quickRfl

theorem mt2 : Nat.beq (runT md kd MT2 (nat_lit 20)) (nat_lit 30) = true := by quickRfl

theorem mt3 : Nat.beq (runT md kd MT3 (nat_lit 30)) (nat_lit 40) = true := by quickRfl

theorem mt4 : Nat.beq (runT md kd MT4 (nat_lit 40)) (nat_lit 50) = true := by quickRfl

theorem mt5 : Nat.beq (runT md kd MT5 (nat_lit 50)) (nat_lit 60) = true := by quickRfl

theorem mt6 : Nat.beq (runT md kd MT6 (nat_lit 60)) (nat_lit 70) = true := by quickRfl

theorem mt7 : Nat.beq (runT md kd MT7 (nat_lit 70)) (nat_lit 80) = true := by quickRfl

theorem mt8 : Nat.beq (runT md kd MT8 (nat_lit 80)) (nat_lit 89) = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
