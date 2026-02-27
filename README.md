# Dafny + LLM Verification Experiments

## Introduction

Goal: The goal was to test whether Claude Sonnet 4.6 can generate verified Dafny code on increasing difficulty levels, going from basic algorithms to research level verification challenges. As AI-assisted programming becomes more common, understanding where LLMs succeed and fail at formal verification is very important. Dafny requires not just correct code but mathematically proven correctness via loop invariants, postconditions, and lemmas. This is the ultimate test on whether LLMs actually "understand" program semantics or merely just pattern matching.

To play around with Dafny to find a project idea, I created 20 batches (40 individual experiments) with increasing difficulty:

Batches 1-10 (Baseline): Classic algorithms (sum, factorial, array operations, intentional bugs) <br>
Batches 11-15 (Moderate): 2D arrays, recursive datatypes, complex quantifiers, non-linear arithmetic, multiset reasoning <br>
Batches 16-18 (Hard): Non-linear division from scratch, ghost state, deep induction lemmas <br>
Batches 19-20 (Extreme): Ghost frame reasoning, quantifier alternation (∀∃), non-structural termination

Each experiment was attempted using Claude Code with iterative prompting. <br>

Success = verification with ≤2 retry attempts. <br>
Failure = parse errors, verification failure, or timeout after 2 attempts.

## Batch Descriptions

Batch 1-2: Basic Arithmetic
Simple recursive functions (Sum, Product, Factorial, Fibonacci) with imperative loop implementations. The goal is to test if Claude knows basic loop invariant patterns.

Batch 3: Intentional Bugs (Optimizations)
Deliberately broken "optimized" versions (swapped operations, stride-2 loops). The goal is to confirm that Dafny catches off-by-one errors that look plausible.

Batch 4-5: Array Min/Max
FindMax, FindMin with witnessed elements and index tracking. The goal is to test quantifier reasoning over array prefixes.

Batch 6: Array Sum with Lemmas
Requires explicit SumSeqAppend lemma to bridge recursive spec with imperative loop. The goal is to test if Claude can write inductive lemmas.

Batch 7: Sequence Operations
Reverse, Append with structural induction lemmas. The goal is to test recursive datatype reasoning.

Batch 8: Injected Bugs
Off by one errors, missing invariants, wrong invariants. Goal is to confirm Dafny's error taxonomy (invariant vs postcondition failures).

Batch 9: Missing/Wrong Invariants
Loops with no invariants, bounds-only, or shifted invariants. The goal is to show invariants are the only info that survives loops.

Batch 10: IsSorted + Binary Search
Quantifier guarding (j+1 < a.Length) and exclusion-zone reasoning. Goal is to see performance on canonical tricky algorithm.

Batch 11: Matrix Operations
2D array transpose and multiplication with nested loop invariants. I wanted to evaluate multi-dimensional reasoning.

Batch 12: Recursive Datatypes
Linked lists and binary trees with decreases clauses. The goal is to test structural termination.

Batch 13: Partition + Nested Quantifiers
Lomuto partition (multiset preservation) and all-pairs check. Wanted to test ghost state (multiset) and nested forall.

Batch 14: Non-Linear Arithmetic
Integer square root via binary search on non-linear predicate. Wanted to push SMT solver limits. (GCD hit token limit)

Batch 15: Multiset + Permutations
Array swap and in-place reversal with multiset equality. The goal is to test permutation reasoning.

Batch 16: Division From Scratch
Implement / and % using only subtraction loops. Goal is to see Non-linear specs without built-in operators. (ModExp hit token limit)

Batch 17: 3 Way Partition + Ghost Sets
Dutch National Flag (3 zones) and duplicate detection with ghost map. The goal was to see performance on a complex ghost state. (Unique_check had parse errors across 3 attempts - ghost variable scoping)

Batch 18: Deep Induction Lemmas
Flatten sequence associativity with manual structural hints. Time to see Research-level lemma complexity. (GCD timed out)

Batch 19: Ghost Frame Reasoning
Ghost history tracking with old() semantics and non-structural decreases. Wanted to test advanced knowledge on Heap frame reasoning. (Ghost_decreases timed out after 8 minutes)

Batch 20: Quantifier Alternation (∀∃)
Forall-exists nested quantifiers (provably hard for SMT). The goal is to find the breaking point. (Both experiments failed verification)

## Results

B1: ✓ ✓ | B2: ✓ ✓ | B3: ✓ ✓ | B4: ✓ ✓ | B5: ✓ ✓ <br>
B6: ✓ ✓ | B7: ✓ ✓ | B8: ✓ ✓ | B9: ✓ ✓ | B10: ✓(r) ✓ <br>
B11: ✓ ✓ | B12: ✓(r) ✓ | B13: ✓ ✓ | B14: ✓ x | B15: ✓ ✓(r) <br>
B16: ✓ x | B17: ✓ x | B18: x ✓ | B19: ✓ x | B20: x x <br>

Key:

✓ = First-try success (verified 0 errors) <br>
✓(r) = Success on 2nd attempt after Claude fix <br>
x = Failed (verification failure, parse error, or timeout)

## Success Rate:

Batches 1-13: 26/26 eventual success (100%) - B10 and B12 each had one experiment needing retry <br>
Batches 14-15: 3/4 (75%) - B14.2 (GCD) hit API token limit <br>
Batches 16-18: 3/6 (50%) - B16.2 (ModExp) token limit, B18.1 (GCD) timeout <br>
Batches 19-20: 1/4 (25%) - B17.2, B19.2, B20.1, B20.2 genuine failures

**Overall: 33/40 (82.5%) eventual success | 30/40 (75%) first-try success**

## Observations

### Phase 1 (B1-B10): Claude Dominated
There was perfect generation of loop invariants for basic algorithms. Claude correctly wrote inductive lemmas (SumSeqAppend, ReverseConsAppend), handled multiset reasoning without hints (Partition), and self-corrected quantifier guards (j+1 < a.Length) on retry.

### Phase 2 (B11-15): Increased Difficulty, Still Strong
Matrix operations (nested loops) were verified first-try. Recursive datatypes needed one decreases clause fix (B12.1). The Dutch National Flag (3-way partition) was verified first-try. In B14.2, GCD hit API token limits due to massive lemma generation, not verification failure. So noting that higher compute could determine success rate, though long time nevertheless.

### Phase 3 (B16-18): First Genuine Weaknesses
**B17.2 (Unique_check): Ghost Variable Scoping Failure**

Claude couldn't figure out ghost var vs var syntax. There were three failed attempts with parse errors:

- Attempt 1: ghost var witness → "invalid Ident"
- Attempt 2: var witness → "invalid Ident" (can't read from ghost map)
- Attempt 3: Back to ghost var witness → same error

Ghost variables require an understanding of Dafny's frame reasoning (heap vs stack). The issue here was Claude treated them as syntax variations, not semantic ideas.

**B16.2 (ModExp)**: Token limit hit during lemma generation <br>
**B18.1 (Flatten GCD)**: Timeout on deep structural induction

### Phase 4 (B19-20): Breaking Point
**B19.1 (Ghost History)**: Succeeded by using a class with ghost field instead of local ghost var. This shows Claude can learn from context about heap state.

**B19.2 (Ghost Decreases)**: Timed out after 8 minutes trying to prove non-structural termination. This is legitimately hard (requires manual lemmas linking ghost parameter to progress).

**B20.1 (Forall-Exists)**: x - Verification failure:

```
Error: a postcondition could not be proved on this return path
ensures result <==> forall i :: 0 <= i < a.Length ==> 
                      exists j :: 0 <= j < b.Length && a[i] == b[j]
```

Here, Claude successfully generated the witness map but couldn't connect it to biconditional postcondition. SMT solver couldn't discharge the <== direction.

**B20.2 (Ghost Seq Quantifier)**: x - Verification failure even after 3 rewrites:

```
Error: a postcondition could not be proved
ensures valid <==> forall i :: 0 <= i < |trace|-1 ==> 
                     exists k :: i < k < |trace| && trace[i] < trace[k]
```

Claude tried a lot of different methods:
- Simple forall accumulation (failed)
- Adding explicit assert bridge (failed)
- Disjunction form p >= i || exists k (still failed)

The cause seems to be that ∀∃ quantifier alternation is just generally hard for SMT. Z3 can't instantiate quantifiers efficiently without explicit witness functions.

## Summary

Claude does well at:
- Loop invariants for standard algorithms (sum, max, partition)
- Structural induction lemmas (append, reverse, flatten)
- Multiset reasoning (Dafny's axioms handle it automatically)
- Nested loops with coordinated invariants (matrix ops)
- Quantifier guards (fixing a[j+1] bounds on retry)
- Non-linear arithmetic (sqrt via binary search)

Claude struggles at:
- Ghost variable scoping (heap vs stack semantics)
- Frame reasoning (what old() captures, modifies clauses for ghost state)
- Non-structural termination (decreases clauses not tied to datatype structure)
- Quantifier alternation (∀∃) - SMT solver bottleneck, not Claude's fault
- Token limits on complex lemmas (GCD, ModExp) - infrastructure issue

## Reflection

I knew LLMs wouldn't fail on concepts beyond basic loops, which was shown on Claude crushing B1-B13 (100% success). It was expected. As the complexity increased, I thought I would see that same performance. It did, be fair, with multi-dimensional reasoning succeeding. However, I began noticing issues in ghost variables. And then it kind of became clear where Claude will struggle:

Failures here are clustered around semantic concepts that need understanding of Dafny's verification model:

- Ghost variables = understanding heap frames
- ∀∃ quantifiers = understanding SMT solver limitations
- Token limits = infrastructure, not intelligence

## Limitations

- Results specific to Claude 4.6 Sonnet. GPT-5/Gemini may differ.
- Didn't test against human students or earlier LLMs.
- Different prompts might have different success rates.
- Some "failures" (GCD, ModExp) were infrastructure, not capability.
- Only tested with iterative prompting (≤2 retries) (batch/parallel generation untested).

## Project Ideas From This Brief Study
### Note: I am happy to move in any direction as best seems fit.

### 1. Understanding Ghost Variable Failures
**Research Question:** Why does Claude fail on ghost variable scoping (B17.2) when it succeeds on syntactically similar non-ghost code?

**Hypothesis:** LLMs lack a coherent mental model of Dafny's heap frame semantics. They treat ghost var as a keyword modifier rather than understanding it marks heap-allocated verification state.

**Proposed Study:**

Design pairs of identical code snippets where only difference is ghost vs non-ghost
- Example: var x := map[key] (fails) vs var x := array[index] (succeeds)

Test across 4 dimensions:
- Heap vs Stack: Local ghost var vs ghost field
- Frame reasoning: old(), modifies, reads clauses
- Contamination flow: Ghost reads forcing ghost writes
- Syntax variations: ghost var witness vs var witness in ghost context

### 2. Quantifier Alternation Failure Modes: LLM vs SMT
**Research Question:** When Claude fails on ∀∃ patterns (B20.1, B20.2), is it because:

(A) Claude can't generate witness functions, OR
(B) SMT solver times out even with correct code?

**Hypothesis:** Failures are bimodal:
- Type 1 (LLM): Claude generates wrong witness strategy (e.g., storing first occurrence instead of any valid witness)
- Type 2 (SMT): Claude generates correct code but Z3 can't instantiate quantifiers

**Proposed Study:**
Phase 1: Isolate the Bottleneck
- Manually fix Claude's failed attempts and re-run verification to determine if failures are due to incorrect code generation or SMT timeout

Phase 2: Systematic ∀∃ Benchmark
- Create new ∀∃ tasks varying in quantifier depth and domain size, testing Claude's success rate and comparing error types (generation failures vs solver timeouts)


### 3. Cross-LLM Verification Benchmark: Is Claude Special?
**Research Question:** Are the failures in B17-B20 Claude-specific or do all LLMs have the same issue?

**Hypothesis:** Ghost variable failures are universal (all LLMs pattern-match syntax), but quantifier failures vary by training data exposure to formal methods.

**Proposed Study:**

Models to Test:
- Claude 4.6 Sonnet
- GPT-5.3-Codex (OpenAI)
- Gemini 3 Pro (Google)
- DeepSeek Coder V3 (open weights, can we probe activations?)
- Control: CodeLlama 70B fine-tuned on Dafny corpus (does training help?)

Dataset: The 40 tasks (B1-B20) + new edge cases focusing on:
- Ghost variable scoping=
- ∀∃ patterns 

Evaluation Protocol:
- Zero-shot: Single prompt, no retries
- Few-shot: Provide 2 working examples of ghost variables
- Self-repair: Allow 2 iterative fixes

Controlling:
- Prompt engineering: Does rephrasing "use ghost variable" to "track verification state on heap" help?
- Chain-of-thought: Force model to explain heap vs stack before generating code
- Retrieval augmentation: Give model access to Dafny docs during generation
