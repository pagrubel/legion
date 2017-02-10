## Issues with oopsla13 paper
  - E-Call seems problematic. It allows concurrent evaluation of the body with
    the evaluation of the arguments, which is nonsense in this call-by-value
    setting. In other words, while there may not be memory dependence, there is
    a value dependence. This shouldn't be hard to fix, just replace the
    valid_interleave to concatenation. Another issue with E-Call is that while
    function calls are part of the expression language, function definitions are
    not. I'm guessing this is because functions are intended to only be defined
    at the top level. Due to these issues, we've temporarily ommitted the call
    rule from the Coq semantics.
  - Values returned by coloring must be colors (ivs) not arbitrary vs
  - We ignore the coherence, as the semantics are only defined for exclusive.
    E-Read is a little strange in the paper in that it is defined as an
    exclusive read even when the read location occurs in the clobber set.
    Shouldn't this be disallowed?
  - Shouldn't we ensure new regions are fresh e.g. for the partition rule? 

## Other thoughts
  - Incomplete, as apply, valid_interleave, and E-Call are not implemented.
  - Lots of semantic rules are ommitted, e.g. tuple, dereference, etc. I'm
    guessing this is intentional as these will be defined by whatever  language
    legion is embedded into. Still, abstracting these away instead of putting
    token placeholders in might be worthwhile.
  - Freeing of memory/and or garbage collection would be nice to be able to
    reason about. 
  - It seems like it should be possible to prove type preservation in the heap
    as an external lemma instead of carrying H around.
  - While I understand the motivation to be a correct concurrent implementation
    of a serial semantics, it seems like it might make some of the reasoning
    challenging, and perhaps explicit concurrency could help? Not sure about
    this though.
  - Are the memory **reduce** operators assumed to be pure? From the apply
    semantics, it would seem that way.
