# Cut

Tested with Agda 2.6.2, Agda standard library 1.7.

- The cut theorem can be found [here](https://github.com/gshen42/cut/blob/main/SeqCalc.agda#L128-L228).
- The proof follows [this lecture note](https://www.cs.cmu.edu/~fp/courses/15317-f17/lectures/10-cutelim.pdf) by Frank Pfenning, except each sequent calculus derivation is indexed by its size to pass Agda's termination check.
- By cut theorem, we can prove [each natural deduction derivation is also a sequent calculus derivation](https://github.com/gshen42/cut/blob/main/SeqCalc.agda#L239-L266), since [sequent calculus is consistent](https://github.com/gshen42/cut/blob/main/SeqCalc.agda#L231-L236), so [natural deduction is also consistent](https://github.com/gshen42/cut/blob/main/SeqCalc.agda#L283-L285).
