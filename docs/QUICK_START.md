# CLARITY Act Deontic Logic Parser - Quick Start Guide

## What is This?

This tool automatically analyzes the CLARITY Act (H.R. 3633) legislation and converts it into formal logic that computers can verify. Think of it as translating legalese into mathematical formulas.

## 5-Minute Quick Start

### 1. Get the Code

```bash
git clone https://github.com/endomorphosis/Clarity_Act_Deontic_Logic.git
cd Clarity_Act_Deontic_Logic
git submodule update --init --recursive
```

### 2. Run the Parser

```bash
bash tools/bootstrap_venv.sh
source .venv/bin/activate
python src/clarity_act_parser.py
```

That's it! You'll get 6 output files in the `outputs/` directory.

### 3. View Results

```bash
# Human-readable summary
cat outputs/clarity_act_analysis_summary.txt

# JSON data for programming
cat outputs/clarity_act_requirements.json

# Formal logic for Lean 4 theorem prover
cat outputs/clarity_act_lean.lean
```

## What Does It Do?

### Input (Legal Text)
```
Digital commodity exchanges MUST register with the CFTC
```

### Output (Formal Logic)
```
O[digital_commodity_exchanges](register_with_cftc)
```

**Translation**: "It is **O**bligatory for digital commodity exchanges to register with CFTC"

## Understanding the Outputs

### 1. Requirements JSON
Lists all 28 requirements in structured format:
```json
{
  "requirement_id": "REG-001",
  "agent": "digital_commodity_exchanges",
  "action": "register_with_the_cftc",
  "requirement_type": "OBLIGATION"
}
```

### 2. Deontic Formulas JSON
Formal logic notation for each requirement:
```json
{
  "formal_notation": "O[exchanges](register)",
  "operator": "O",  // O = Obligation, F = Forbidden, P = Permitted
  "natural_language": "Exchanges must register"
}
```

### 3. Lean 4 File
Code for the Lean theorem prover:
```lean
axiom REG_001 : Obligatory Agent.DigitalCommodityExchange (True)
```

### 4. Coq File
Code for the Coq theorem prover:
```coq
Axiom REG_001 : Obligatory True.
```

### 5. SMT-LIB File
Code for SMT solvers like Z3:
```smt
(assert (obligatory DigitalCommodityExchange true))
```

### 6. Summary Text File
Human-readable analysis with statistics

## Key Statistics

The CLARITY Act contains:
- **28 requirements** total
- **23 obligations** (must do)
- **4 prohibitions** (must not do)
- **1 permission** (may do)

Organized across:
- Registration & Reporting (6)
- Trade Market Integrity (8)
- Decentralized Governance (3)
- Rulemaking (3)
- AML/Bank Secrecy (3)
- Jurisdiction (3)
- Federal Reserve Restrictions (2)

## Interactive Usage

Try the example script:

```bash
python example_usage.py
```

This shows how to:
- Query requirements by section
- Filter by agent (exchanges, brokers, etc.)
- Find prohibitions
- Extract temporal constraints
- Get formal logic notation

## Common Use Cases

### Use Case 1: Check What Exchanges Must Do

```python
from clarity_act_parser import ClarityActParser

parser = ClarityActParser("data/clarity_act_summary.txt")
requirements = parser.parse_document()

exchange_reqs = [r for r in requirements if "exchanges" in r.agent]
for req in exchange_reqs:
    print(f"- {req.text}")
```

### Use Case 2: Find All Prohibitions

```python
formulas = parser.convert_to_deontic_logic()
prohibitions = [f for f in formulas if f['operator'] == 'F']

for p in prohibitions:
    print(f"Prohibited: {p['natural_language']}")
```

### Use Case 3: Export for Compliance System

```python
import json

with open('outputs/clarity_act_requirements.json', 'r') as f:
    requirements = json.load(f)

# Use in your compliance checking system
for req in requirements:
    if req['agent'] == 'your_organization_type':
        check_compliance(req)
```

## Key Concepts

### Deontic Logic Operators

| Symbol | Meaning | Example |
|--------|---------|---------|
| **O** | Obligation (must) | O[agent](action) = "agent must do action" |
| **P** | Permission (may) | P[agent](action) = "agent may do action" |
| **F** | Prohibition (must not) | F[agent](action) = "agent must not do action" |

### Formal Notation Format

```
OPERATOR[agent]((conditions) → action)
```

**Example**:
```
O[sec]((within_270_days) → issue_rules)
```
Means: "SEC is obligated to issue rules within 270 days"

## What Can You Do With This?

1. **Automated Compliance Checking**: Build systems that verify if actions comply with the law
2. **Policy Analysis**: Compare different regulatory approaches
3. **Education**: Teach students about formal methods in law
4. **Research**: Study regulatory complexity and consistency
5. **Software Development**: Build compliant blockchain systems
6. **Legal Tech**: Integrate into legal analysis tools

## Next Steps

### Learn More
- Read [TECHNICAL_DOCUMENTATION.md](docs/TECHNICAL_DOCUMENTATION.md) for details
- See [ipfs_datasets_py Legal Guide](https://github.com/endomorphosis/ipfs_datasets_py/blob/main/docs/guides/LEGAL_DEONTIC_LOGIC_USER_GUIDE.md)

### Extend the System
- Add more sophisticated parsing
- Implement conflict detection
- Build compliance verification
- Create interactive query interface

### Contribute
- Report issues on GitHub
- Suggest improvements
- Add support for other legislation

## Troubleshooting

**Q: Import errors when running?**
A: The parser has fallback implementations. It works without dependencies, but for full features install: `pip install beartype`

**Q: Where does the CLARITY Act text come from?**
A: From `data/clarity_act_summary.txt` - a structured summary of the bill's requirements

**Q: Can I analyze other legislation?**
A: Yes! Create a similar summary file and modify the parser's section methods

**Q: What's a theorem prover?**
A: Software that can mathematically verify logical statements. Lean, Coq, and SMT solvers are examples.

**Q: Why three different formats?**
A: Different theorem provers have different strengths. Lean for modern mathematics, Coq for constructive proofs, SMT for automated verification.

## Support

- Issues: https://github.com/endomorphosis/Clarity_Act_Deontic_Logic/issues
- Discussions: https://github.com/endomorphosis/Clarity_Act_Deontic_Logic/discussions

## Credits

- Parser implementation: This project
- Deontic logic framework: [ipfs_datasets_py](https://github.com/endomorphosis/ipfs_datasets_py)
- CLARITY Act: 119th Congress, H.R. 3633

---

**Ready to start?** Run `python src/clarity_act_parser.py` and explore the outputs!
