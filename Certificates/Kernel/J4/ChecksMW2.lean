module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

theorem mw20 : Nat.beq (runM md kd MW20 (nat_lit 163208765248)) (nat_lit 176093667536) = true := by quickRfl

theorem mw21 : Nat.beq (runM md kd MW21 (nat_lit 176093667536)) (nat_lit 193273537120) = true := by quickRfl

theorem mw22 : Nat.beq (runM md kd MW22 (nat_lit 193273537120)) (nat_lit 214748374000) = true := by quickRfl

theorem mw23 : Nat.beq (runM md kd MW23 (nat_lit 214748374000)) (nat_lit 227633276288) = true := by quickRfl

theorem mw24 : Nat.beq (runM md kd MW24 (nat_lit 227633276288)) (nat_lit 244813145872) = true := by quickRfl

theorem mw25 : Nat.beq (runM md kd MW25 (nat_lit 244813145872)) (nat_lit 261993015456) = true := by quickRfl

theorem mw26 : Nat.beq (runM md kd MW26 (nat_lit 261993015456)) (nat_lit 279172885040) = true := by quickRfl

theorem mw27 : Nat.beq (runM md kd MW27 (nat_lit 279172885040)) (nat_lit 296352754624) = true := by quickRfl

theorem mw28 : Nat.beq (runM md kd MW28 (nat_lit 296352754624)) (nat_lit 313532624208) = true := by quickRfl

theorem mw29 : Nat.beq (runM md kd MW29 (nat_lit 313532624208)) (nat_lit 330712493792) = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
