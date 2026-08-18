"""Bounded check of the 'no elementary antiderivative' side-claim.
IMPORTANT distinction this establishes regardless of outcome:
  - 'the INDEFINITE integral has no elementary antiderivative'  (Risch question)
  - 'the DEFINITE integral is not a combination of named constants' (PSLQ question)
are different questions.  Our 583,330-call PSLQ search already answered the second
(negative).  The first is what the write-up's Risch argument is about."""
import sympy as sp, signal
x=sp.symbols('x', real=True, positive=True)
A=x**4+4*x**2+1; E=x**4+4*x**2+9
f=2*(x**4+6*x**2+3)/(sp.sqrt(A)*E)
g=-(x**4*E)/(2*A)
integrand=f*sp.exp(g)
print("integrand =", integrand)
print("\nStructure: e^{g} * f with g RATIONAL but f ALGEBRAIC (contains sqrt(x^4+4x^2+1)).")
print("So the classical Liouville criterion for INT f e^g dx with f,g rational")
print("(elementary iff exists rational T with f = T' + g' T) does NOT apply directly:")
print("we are in the algebraic extension Q(x, sqrt(x^4+4x^2+1)), where deciding")
print("elementarity needs Risch for algebraic function fields.")
def timeout(s,fr): raise TimeoutError
signal.signal(signal.SIGALRM,timeout)
for name,fn in (("integrate", lambda: sp.integrate(integrand,x)),
                ("risch_integrate", lambda: sp.risch_integrate(integrand,x))):
    signal.alarm(180)
    try:
        r=fn(); print(f"\nsympy {name}: returned {type(r)}")
        print("   ", str(r)[:200])
    except Exception as e:
        print(f"\nsympy {name}: FAILED/UNEVALUATED -> {type(e).__name__}: {str(e)[:120]}")
    finally:
        signal.alarm(0)
print("\nCONCLUSION: sympy failing proves NOTHING (it is incomplete on algebraic")
print("extensions).  The claim is re-flagged UNVERIFIED, not refuted.")
