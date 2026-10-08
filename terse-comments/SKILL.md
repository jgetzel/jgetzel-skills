---
name: terse-comments
description: Comment style — a comment answers "what is this?", nothing else. Use whenever writing, editing, or reviewing code comments or docstrings in any language, and when adding code to an existing file. Also use when the user says "terse comments", "comment style", "too many comments", "fix these comments", or complains about comment noise, narration, or over-commenting.
---

# Terse comments

A comment answers **"what is this?"** — what this code is, or the outside
constraint that shapes it. Nothing else.

## Write comments for

- What a block does, when the code alone doesn't say it.
- A constraint from outside the codebase: a bank's alert wording, an API's
  fixed format, a platform limit, a trap that looks wrong but isn't.
- A sample of real input a regex is written against.

The model for the trap case:

```js
// toISOString() is UTC — a local evening date lands on tomorrow.
```

Names the trap, and carries enough that a skeptical reader won't delete the
line. Not a paragraph defending it.

## Don't write comments that

- **Defend a choice.** State what the code does; don't argue for it. If a
  decision needs a paragraph, it belongs in the README.
- **Describe how the code changed** — "the whole point of the refactor",
  "previously hardcoded", "we used to". That's git's job.
- **Describe what doesn't exist yet** — "no savings alert has been seen",
  "unverified". Absence isn't documentation.
- **Describe what the code will become.** Future work goes in `TODO.md`.

One or two lines. If a comment runs to a paragraph, it's arguing.

## Docs

- `README.md` — how it works today.
- `TODO.md` — known problems and planned work.
- git — how it got here.

Keep them short. Don't restate a mechanism in more than one place.
