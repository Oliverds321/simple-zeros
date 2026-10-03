/-
Node R3 (L7_1): the ANALYTIC half of Track R — the real-valued Shell functional of a polynomial profile equals the
exact rational `CertQ.shellBq` (ssec:shell-cert "Method", sec_shell.tex l.1027–1031:
`B(v_p) = (ψ̃(0) + 2∫₀¹ αψ̃ + 2ℓ∫₁^{α′} ψ̃ + 2C⁺∫_{α′}^{λ} ψ̃)/(∫P)²`; here in y-units, see `ShellCertQ.lean`).
Checked numerically [C]: `shell_cert_y.py` reproduces R8-2's `check_profile.py` exactly for S53-L75 and D53-L75.
Dependencies: none new. Template: `ZetaQ.Payoff` §3b (`kernel_psi_eq_double`, `B0_add_B1_half`) and §3c
(`integral_evalPoly_Q`). Difficulty: M–H (Fubini to the double integral; `t = (λ/2)y`; `ψ` even and supported in
`[−λ, λ]`; the polynomial identity for `ψ̂` on `[0, 2]`; soundness of the list-polynomial operations).
-/
import ZetaShell.Interfaces
import ZetaShell.Cert.ShellCertQ
import ZetaShell.Cert.TR_Bshell

/-! PROVED by L7_5 (28 Sep 2026), route (i) of the architect's §6: soundness of the certificate's OWN list code
(`ShellCertQ` unchanged), so the kernel-checked `CertQ.BS53_le`/`BD53_le` apply to the same object.
Sub-lemmas (one file each): `TR_Poly` (univariate `padd`/`pscal`/`pmul`/`peval`/`pint`/`pdefint`/`spread`,
`S.p` as a polynomial in `s = (2t/λ)²`, `mass = (λ/2)·Z`), `TR_Biv` (bivariate Horner code and `psiHat`:
`ψ̂(β) = ∫_{-1}^{1-β} P̂(y)P̂(y+β) dy`), `TR_Psi` (`ψ` even, supported in `[-λ, λ]`, and equal to
`(λ/2)ψ̂(α/(λ/2))/mass²` on `[0, λ]`, change of variables `t = (λ/2)y + α`), `TR_Bshell` (`∫ k ψ = 2∫_{(0,∞)} k ψ`,
split at `1` and `α′`, `α = (λ/2)β`, algebra). The hypothesis `h3 : λ < 2` is not used. -/

namespace ZetaShell

theorem Bshell_eq_shellBq (S : ShellProfile) (h1 : 1 < S.alphaP) (h2 : S.alphaP < S.lam) (h3 : S.lam < 2)
    (hm : 0 < S.mass) :
    Bshell S.level S.alphaP S.Cplus S.v
      = ((CertQ.shellBq S.lam S.alphaP S.level S.Cplus S.d : ℚ) : ℝ) :=
  TR.Bshell_eq_shellBq' S h1 h2 hm

end ZetaShell
