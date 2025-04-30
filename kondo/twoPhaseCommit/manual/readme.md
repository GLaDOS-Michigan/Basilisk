# Readme

Two Phase Commit on asynchronous network.
Observe that in this case, because there is no history, we cannot apply message invariant templates.
Rather, message invariants must still be handcrafted.

More specifically, we cannot write the invariant

> for all `Decide` message `m`, `NextDecisionStepSendFunc` is true of `m.src`

because it is simply not true --- the enabling condition in `NextDecisionStepSendFunc` is no longer true
once the message is sent.
