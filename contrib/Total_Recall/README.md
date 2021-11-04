# Total Recall
This is utility to enable better support for overriding of syntax notation in Isabelle/HOL, developed by Dr Frank Zeyda. In Isabelle, one can remove previously added syntax notation using command like `no_syntax` and `no_notation`. However, these notational changes are not preserved by the theory import mechanism, and so conflicts can arise. 

For example, let's say I'd like to remove some syntax defined in theory `Main`. I can do that using `no_notation` in another theory `A` that imports `Main`. But then let's say I have a other theory `B` that imports both `A` and a further thory `C` (a library, for example) that also imports `Main`. In this case, the overriden syntax would not be preserved, and syntax ambiguity errors arise.

The Total Recall utility overcomes this situation by allowing previously overriden syntax to be totally recalled (hence the name). There are three new commands:

* `purge_syntax` -- corresponds to `no_syntax`, but with support for recalling previous changes
* `purge_notation` -- similar functionality to `no_notation`
* `recall_syntax` -- used at the beginning of a new theory, recalls previously purged syntax notations
