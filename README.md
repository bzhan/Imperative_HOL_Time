# Imperative_HOL_Time
Verifying asymptotic time complexity of imperative programs in Isabelle/HOL.

Paper at: https://arxiv.org/abs/1802.01336

The paper corresponds to the initial commit 8d336cd, which uses the version
of auto2 (https://github.com/bzhan/auto2) at commit 167808b and Isabelle2017.

Last version for Isabelle2018 is c0ca7cb, corresponds to commit b4b629e in auto2 (https://github.com/bzhan/auto2) and Isabelle2018.

The latest commit uses Auto2-HOL and Auto2-Imperative-HOL from the AFP as well as Isabelle2019.

### Abstract:

We present a framework in Isabelle for verifying asymptotic time
complexity of imperative programs. We build upon an extension of
Imperative HOL and its separation logic to include running
time. In addition to the basic arguments, our framework is able
to handle advanced techniques for time complexity analysis, such
as the use of the Akra-Bazzi theorem and amortized
analysis. Various automation is built and incorporated into the
auto2 prover to reason about separation logic with time credits,
and to derive asymptotic behavior of functions. As case studies,
we verify the asymptotic time complexity (in addition to
functional correctness) of imperative algorithms and data
structures such as median of medians selection, Karatsuba's
algorithm, and splay trees.


### License

Copyright (c) 2019, Bohua Zhan and Maximilian P. L. Haslbeck
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those
of the authors and should not be interpreted as representing official policies,
either expressed or implied, of the FreeBSD Project.
