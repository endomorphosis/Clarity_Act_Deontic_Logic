# CLARITY Act Deontic Logic Parser

Automated parsing and formal analysis of the CLARITY Act (H.R. 3633 - Digital Asset Market Clarity Act of 2025) using deontic logic formalism.

## Overview

This project uses the [ipfs_datasets_py](https://github.com/endomorphosis/ipfs_datasets_py) legal deontic logic framework to parse the CLARITY Act legislation and convert its requirements into formal deontic logic representations. The system extracts obligations, permissions, and prohibitions from the bill and generates outputs compatible with multiple theorem provers (Lean 4, Coq, SMT-LIB).

## Features

- ✅ **Automated Requirement Extraction**: Parses legal text to identify MUST, SHALL, MAY, and MUST NOT clauses
- ✅ **Deontic Logic Conversion**: Converts requirements into formal deontic logic notation (O, P, F operators)
- ✅ **Multi-Theorem Prover Support**: Generates output for Lean 4, Coq, and SMT-LIB
- ✅ **Structured Analysis**: Organizes requirements by section and type
- ✅ **Agent-Based Modeling**: Tracks obligations by regulatory agent (CFTC, SEC, exchanges, etc.)
- ✅ **Temporal Reasoning**: Extracts and models time-based constraints (e.g., 270-day rulemaking deadline)

## CLARITY Act Analysis Results

The parser has analyzed the Digital Asset Market Clarity Act of 2025 and extracted:

- **28 Total Requirements**
  - 23 Obligations (MUST/SHALL requirements)
  - 4 Prohibitions (MUST NOT requirements)
  - 1 Permission (MAY clauses)

### Requirements by Section:
- Registration and Reporting: 6 requirements
- Trade Market Integrity: 8 requirements
- Decentralized Governance: 3 requirements
- Rulemaking Implementation: 3 requirements
- AML/Bank Secrecy: 3 requirements
- Jurisdiction: 3 requirements
- Federal Reserve Restrictions: 2 requirements

## Installation

### Prerequisites

- Python 3.8 or higher
- Git

### Setup

```bash
# Clone the repository
git clone https://github.com/endomorphosis/Clarity_Act_Deontic_Logic.git
cd Clarity_Act_Deontic_Logic

# Initialize and update the submodule
git submodule update --init --recursive

# (Optional) Install additional dependencies for enhanced features
pip install beartype  # For full logic_integration support
```

## Usage

### Basic Usage

Run the parser to analyze the CLARITY Act:

```bash
python src/clarity_act_parser.py
```

This will generate several output files in the `outputs/` directory:

- `clarity_act_requirements.json` - Structured requirements with metadata
- `clarity_act_deontic_formulas.json` - Formal deontic logic representations
- `clarity_act_lean.lean` - Lean 4 theorem prover output
- `clarity_act_coq.v` - Coq theorem prover output
- `clarity_act_smt.smt2` - SMT-LIB solver input
- `clarity_act_analysis_summary.txt` - Human-readable summary

### Example Output

#### Deontic Logic Notation

```
O[digital_commodity_exchanges](register_with_cftc)
```
*Translation: Digital commodity exchanges are obligated to register with the CFTC*

#### Lean 4 Format

```lean
axiom REG_001_register_with_the_cftc : 
  Obligatory Agent.DigitalCommodityExchanges (True)
```

#### Natural Language

```
The digital commodity exchanges is obligated to register with the cftc.
```

## Project Structure

```
Clarity_Act_Deontic_Logic/
├── src/
│   └── clarity_act_parser.py      # Main parser implementation
├── data/
│   └── clarity_act_summary.txt    # CLARITY Act requirements summary
├── outputs/                        # Generated analysis results
│   ├── clarity_act_requirements.json
│   ├── clarity_act_deontic_formulas.json
│   ├── clarity_act_lean.lean
│   ├── clarity_act_coq.v
│   ├── clarity_act_smt.smt2
│   └── clarity_act_analysis_summary.txt
├── docs/                           # Documentation
├── ipfs_datasets_py/              # Submodule: Legal deontic logic framework
└── README.md
```

## Deontic Logic Framework

This project uses the legal deontic logic framework from [ipfs_datasets_py](https://github.com/endomorphosis/ipfs_datasets_py). See the [Legal Deontic Logic User Guide](https://github.com/endomorphosis/ipfs_datasets_py/blob/main/docs/guides/LEGAL_DEONTIC_LOGIC_USER_GUIDE.md) for more information.

### Deontic Operators

- **O (Obligation)**: Agent MUST perform action
- **P (Permission)**: Agent MAY perform action
- **F (Prohibition)**: Agent MUST NOT perform action
- **R (Right)**: Agent has the right to perform action

## CLARITY Act Key Provisions

### 1. Registration Requirements
- Digital commodity exchanges, brokers, and dealers MUST register with CFTC
- Issuers MUST disclose blockchain maturity and financial condition
- SEC MUST certify mature blockchain systems

### 2. Market Integrity
- Exchanges MUST implement trade monitoring and recordkeeping
- Brokers/dealers MUST maintain risk management and capital requirements
- Customer assets MUST NOT be commingled

### 3. Governance
- Decentralized systems MUST NOT be treated as single-entity controlled
- Governance changes REQUIRE updated certifications

### 4. Rulemaking
- SEC and CFTC MUST issue rules within 270 days of enactment

### 5. AML/BSA Compliance
- All registered entities MUST implement AML and counter-terrorism programs

### 6. Federal Reserve Restrictions
- Federal Reserve MUST NOT offer CBDCs directly to individuals
- CBDCs MUST NOT be used for monetary policy operations

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests.

## License

This project analyzes public domain legislation (CLARITY Act H.R. 3633). The code is provided as-is for research and educational purposes.

## References

- [CLARITY Act (H.R. 3633) on Congress.gov](https://www.congress.gov/bill/119th-congress/house-bill/3633)
- [ipfs_datasets_py Legal Deontic Logic Framework](https://github.com/endomorphosis/ipfs_datasets_py)
- [Legal Deontic Logic User Guide](https://github.com/endomorphosis/ipfs_datasets_py/blob/main/docs/guides/LEGAL_DEONTIC_LOGIC_USER_GUIDE.md)

## Citation

If you use this work in your research, please cite:

```
CLARITY Act Deontic Logic Parser
Digital Asset Market Clarity Act of 2025 (H.R. 3633)
https://github.com/endomorphosis/Clarity_Act_Deontic_Logic
```
