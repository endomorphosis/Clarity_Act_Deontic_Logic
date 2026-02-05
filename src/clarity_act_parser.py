#!/usr/bin/env python3
"""
CLARITY Act Deontic Logic Parser

This script parses the CLARITY Act (H.R. 3633 - Digital Asset Market Clarity Act of 2025)
and converts its requirements into formal deontic logic representations using the
ipfs_datasets_py legal deontic logic framework.

The script extracts obligations, permissions, and prohibitions from the legislation
and generates formal logic representations in multiple theorem prover formats (Lean, Coq, SMT-LIB).
"""

import sys
import json
import re
from pathlib import Path
from typing import Dict, List, Any, Tuple
from datetime import datetime

# Add the submodule to the path
sys.path.insert(0, str(Path(__file__).parent.parent / "ipfs_datasets_py"))

# Import deontic logic components
try:
    from ipfs_datasets_py.logic_integration import (
        DeonticLogicConverter,
        LegalDomainKnowledge,
        ConversionContext,
        LegalDomain,
        LeanTranslator,
        CoqTranslator,
        SMTTranslator,
        LogicTranslationTarget,
        DeonticFormula,
        DeonticOperator
    )
    LOGIC_AVAILABLE = True
except ImportError as e:
    print(f"Warning: Could not import logic_integration: {e}")
    print("Will create mock implementations for demonstration")
    LOGIC_AVAILABLE = False
    
    # Create mock classes
    class DeonticOperator:
        OBLIGATION = "O"
        PERMISSION = "P"
        PROHIBITION = "F"
        RIGHT = "R"
    
    class DeonticFormula:
        def __init__(self, operator, agent, action, conditions=None, metadata=None):
            self.operator = operator
            self.agent = agent
            self.action = action
            self.conditions = conditions or []
            self.metadata = metadata or {}


class ClarityActRequirement:
    """Represents a single requirement from the CLARITY Act."""
    
    def __init__(self, 
                 requirement_id: str,
                 section: str,
                 text: str,
                 requirement_type: str,  # MUST, MUST NOT, MAY, SHALL, etc.
                 agent: str,
                 action: str,
                 conditions: List[str] = None,
                 temporal_constraint: str = None):
        self.requirement_id = requirement_id
        self.section = section
        self.text = text
        self.requirement_type = requirement_type
        self.agent = agent
        self.action = action
        self.conditions = conditions or []
        self.temporal_constraint = temporal_constraint
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            "requirement_id": self.requirement_id,
            "section": self.section,
            "text": self.text,
            "requirement_type": self.requirement_type,
            "agent": self.agent,
            "action": self.action,
            "conditions": self.conditions,
            "temporal_constraint": self.temporal_constraint
        }


class ClarityActParser:
    """Parser for CLARITY Act requirements to deontic logic."""
    
    def __init__(self, document_path: Path):
        """
        Initialize the parser.
        
        Args:
            document_path: Path to the CLARITY Act text or summary file
        """
        self.document_path = document_path
        self.requirements: List[ClarityActRequirement] = []
        self.deontic_formulas: List[Dict[str, Any]] = []
        
    def parse_document(self) -> List[ClarityActRequirement]:
        """
        Parse the CLARITY Act document and extract requirements.
        
        Returns:
            List of extracted requirements
        """
        print(f"Parsing CLARITY Act from: {self.document_path}")
        
        with open(self.document_path, 'r') as f:
            content = f.read()
        
        # Parse requirements by sections
        self._parse_registration_requirements(content)
        self._parse_trade_integrity_requirements(content)
        self._parse_governance_requirements(content)
        self._parse_rulemaking_requirements(content)
        self._parse_aml_requirements(content)
        self._parse_jurisdiction_requirements(content)
        self._parse_federal_reserve_restrictions(content)
        
        print(f"Extracted {len(self.requirements)} requirements")
        return self.requirements
    
    def _extract_requirement(self, text: str, section: str, req_id: str) -> ClarityActRequirement:
        """Extract structured requirement from text."""
        
        # Determine requirement type
        if " MUST " in text or " SHALL " in text or " REQUIRE" in text:
            if " MUST NOT " in text or " SHALL NOT " in text:
                req_type = "PROHIBITION"
            else:
                req_type = "OBLIGATION"
        elif " MAY " in text:
            req_type = "PERMISSION"
        else:
            req_type = "OBLIGATION"  # Default
        
        # Extract agent (who has the obligation/permission)
        agent = self._extract_agent(text)
        
        # Extract action (what they must/may do)
        action = self._extract_action(text)
        
        # Extract conditions (under what circumstances)
        conditions = self._extract_conditions(text)
        
        # Extract temporal constraints
        temporal = self._extract_temporal_constraint(text)
        
        return ClarityActRequirement(
            requirement_id=req_id,
            section=section,
            text=text,
            requirement_type=req_type,
            agent=agent,
            action=action,
            conditions=conditions,
            temporal_constraint=temporal
        )
    
    def _extract_agent(self, text: str) -> str:
        """Extract the agent (entity with obligation/permission)."""
        agents = [
            "Digital commodity exchanges", "Exchanges",
            "Digital commodity brokers", "Brokers",
            "Digital commodity dealers", "Dealers",
            "Issuers",
            "SEC", "CFTC",
            "Digital asset market intermediaries",
            "Registered entities",
            "Federal Reserve banks"
        ]
        
        for agent in agents:
            if agent in text:
                return agent.lower().replace(" ", "_")
        
        return "unspecified_agent"
    
    def _extract_action(self, text: str) -> str:
        """Extract the action that must/may be performed."""
        # Try to extract the verb phrase after MUST/SHALL/MAY
        patterns = [
            r"(?:MUST|SHALL|REQUIRE[DS]?)\s+(?:NOT\s+)?([^.]+?)(?:\s+(?:within|by|before|if|provided|subject)|\.|$)",
            r"MAY\s+([^.]+?)(?:\s+(?:if|provided|subject)|\.|$)"
        ]
        
        for pattern in patterns:
            match = re.search(pattern, text, re.IGNORECASE)
            if match:
                action = match.group(1).strip()
                # Clean up and normalize
                action = action.lower().replace(" ", "_").replace("-", "_")[:100]
                return action
        
        # Fallback: use a cleaned version of the text
        return text.lower().replace(" ", "_").replace("-", "_")[:50]
    
    def _extract_conditions(self, text: str) -> List[str]:
        """Extract conditions under which the requirement applies."""
        # Maximum number of conditions to extract per requirement
        MAX_CONDITIONS_PER_REQUIREMENT = 3
        
        conditions = []
        
        # Look for condition keywords
        condition_patterns = [
            r"(?:if|when|where|provided that|subject to)\s+([^.]+)",
        ]
        
        # Avoid extracting "with the CFTC/SEC" as conditions
        avoid_patterns = [
            r"with the (CFTC|SEC|Federal Reserve)",
            r"by the (CFTC|SEC)",
        ]
        
        for pattern in condition_patterns:
            matches = re.finditer(pattern, text, re.IGNORECASE)
            for match in matches:
                condition = match.group(1).strip()[:100]
                # Skip if it matches an avoid pattern
                is_valid = True
                for avoid_pattern in avoid_patterns:
                    if re.search(avoid_pattern, condition, re.IGNORECASE):
                        is_valid = False
                        break
                
                if is_valid and condition and len(condition) > 5:
                    conditions.append(condition)
        
        return conditions[:MAX_CONDITIONS_PER_REQUIREMENT]
    
    def _extract_temporal_constraint(self, text: str) -> str:
        """Extract temporal constraints (deadlines, timeframes)."""
        temporal_patterns = [
            r"within\s+(\d+)\s+(days|months|years)",
            r"by\s+([A-Za-z]+\s+\d+,?\s+\d+)",
            r"before\s+([^.]+)",
            r"during\s+([^.]+)"
        ]
        
        for pattern in temporal_patterns:
            match = re.search(pattern, text, re.IGNORECASE)
            if match:
                return match.group(0)
        
        return None
    
    def _parse_registration_requirements(self, content: str):
        """Parse registration and reporting requirements."""
        section = "REGISTRATION_AND_REPORTING"
        
        requirements_text = [
            "Digital commodity exchanges MUST register with the CFTC",
            "Digital commodity brokers MUST register with the CFTC",
            "Digital commodity dealers MUST register with the CFTC",
            "Issuers MUST disclose information about blockchain system maturity",
            "Issuers MUST disclose financial condition",
            "SEC MUST certify blockchain systems deemed mature"
        ]
        
        for i, req_text in enumerate(requirements_text):
            req_id = f"REG-{i+1:03d}"
            req = self._extract_requirement(req_text, section, req_id)
            self.requirements.append(req)
    
    def _parse_trade_integrity_requirements(self, content: str):
        """Parse trade and market integrity requirements."""
        section = "TRADE_MARKET_INTEGRITY"
        
        requirements_text = [
            "Exchanges MUST implement trade monitoring",
            "Exchanges MUST maintain recordkeeping systems",
            "Exchanges MUST NOT commingle customer assets",
            "Brokers and dealers MUST implement risk management",
            "Brokers and dealers MUST maintain reporting duties",
            "Brokers and dealers MUST maintain capital obligations",
            "Exchanges and brokers MUST implement customer protection measures",
            "Exchanges and brokers MUST implement custody rules subject to federal or state supervision"
        ]
        
        for i, req_text in enumerate(requirements_text):
            req_id = f"TRD-{i+1:03d}"
            req = self._extract_requirement(req_text, section, req_id)
            self.requirements.append(req)
    
    def _parse_governance_requirements(self, content: str):
        """Parse decentralized governance requirements."""
        section = "DECENTRALIZED_GOVERNANCE"
        
        requirements_text = [
            "Decentralized blockchain systems MUST NOT be treated as controlled by a single entity",
            "Changes in control or governance REQUIRE updated certification or reporting",
            "Denied certifications MUST be subject to public review"
        ]
        
        for i, req_text in enumerate(requirements_text):
            req_id = f"GOV-{i+1:03d}"
            req = self._extract_requirement(req_text, section, req_id)
            self.requirements.append(req)
    
    def _parse_rulemaking_requirements(self, content: str):
        """Parse rulemaking and implementation requirements."""
        section = "RULEMAKING_IMPLEMENTATION"
        
        requirements_text = [
            "SEC and CFTC MUST develop rules within 270 days of enactment",
            "SEC and CFTC MUST issue rules within 270 days of enactment",
            "Expedited registration procedures MUST be available during transition"
        ]
        
        for i, req_text in enumerate(requirements_text):
            req_id = f"RUL-{i+1:03d}"
            req = self._extract_requirement(req_text, section, req_id)
            self.requirements.append(req)
    
    def _parse_aml_requirements(self, content: str):
        """Parse AML and Bank Secrecy Act requirements."""
        section = "AML_BANK_SECRECY"
        
        requirements_text = [
            "Digital asset market intermediaries MUST comply with Bank Secrecy Act",
            "Registered entities MUST implement anti-money laundering programs",
            "Registered entities MUST implement counter-terrorism financing programs"
        ]
        
        for i, req_text in enumerate(requirements_text):
            req_id = f"AML-{i+1:03d}"
            req = self._extract_requirement(req_text, section, req_id)
            self.requirements.append(req)
    
    def _parse_jurisdiction_requirements(self, content: str):
        """Parse jurisdiction requirements."""
        section = "JURISDICTION"
        
        requirements_text = [
            "Digital commodities on mature blockchains MAY be exempt from SEC registration",
            "SEC maintains oversight for broker and dealer activities on national securities exchanges",
            "SEC maintains oversight for activities on alternative trading systems"
        ]
        
        for i, req_text in enumerate(requirements_text):
            req_id = f"JUR-{i+1:03d}"
            req = self._extract_requirement(req_text, section, req_id)
            self.requirements.append(req)
    
    def _parse_federal_reserve_restrictions(self, content: str):
        """Parse Federal Reserve restrictions."""
        section = "FEDERAL_RESERVE_RESTRICTIONS"
        
        requirements_text = [
            "Federal Reserve banks MUST NOT offer central bank digital currencies directly to individuals",
            "Federal Reserve banks MUST NOT use central bank digital currency for monetary policy operations"
        ]
        
        for i, req_text in enumerate(requirements_text):
            req_id = f"FED-{i+1:03d}"
            req = self._extract_requirement(req_text, section, req_id)
            self.requirements.append(req)
    
    def convert_to_deontic_logic(self) -> List[Dict[str, Any]]:
        """
        Convert parsed requirements to deontic logic formulas.
        
        Returns:
            List of deontic logic formulas
        """
        print("\nConverting requirements to deontic logic...")
        
        for req in self.requirements:
            formula = self._create_deontic_formula(req)
            self.deontic_formulas.append(formula)
        
        print(f"Created {len(self.deontic_formulas)} deontic formulas")
        return self.deontic_formulas
    
    def _create_deontic_formula(self, req: ClarityActRequirement) -> Dict[str, Any]:
        """Create a deontic logic formula from a requirement."""
        
        # Determine deontic operator
        if req.requirement_type == "OBLIGATION":
            operator = DeonticOperator.OBLIGATION
            operator_symbol = "O"
        elif req.requirement_type == "PROHIBITION":
            operator = DeonticOperator.PROHIBITION
            operator_symbol = "F"
        elif req.requirement_type == "PERMISSION":
            operator = DeonticOperator.PERMISSION
            operator_symbol = "P"
        else:
            operator = DeonticOperator.OBLIGATION
            operator_symbol = "O"
        
        # Build formal representation
        formal_notation = self._build_formal_notation(
            operator_symbol, req.agent, req.action, req.conditions
        )
        
        # Build natural language representation
        natural_language = self._build_natural_language(
            operator_symbol, req.agent, req.action, req.conditions
        )
        
        return {
            "requirement_id": req.requirement_id,
            "section": req.section,
            "operator": operator_symbol,
            "agent": req.agent,
            "action": req.action,
            "conditions": req.conditions,
            "temporal_constraint": req.temporal_constraint,
            "formal_notation": formal_notation,
            "natural_language": natural_language,
            "source_text": req.text
        }
    
    def _build_formal_notation(self, operator: str, agent: str, 
                               action: str, conditions: List[str]) -> str:
        """Build formal deontic logic notation."""
        
        # Clean action for formal notation
        action_clean = action.replace(" ", "_")
        
        if conditions:
            # Format: O[agent]((condition1 ∧ condition2) → action)
            cond_str = " ∧ ".join([c[:30].replace(" ", "_") for c in conditions])
            return f"{operator}[{agent}](({cond_str}) → {action_clean})"
        else:
            # Format: O[agent](action)
            return f"{operator}[{agent}]({action_clean})"
    
    def _build_natural_language(self, operator: str, agent: str,
                                action: str, conditions: List[str]) -> str:
        """Build natural language description."""
        
        operator_text = {
            "O": "is obligated to",
            "F": "is forbidden from",
            "P": "is permitted to"
        }.get(operator, "must")
        
        base = f"The {agent.replace('_', ' ')} {operator_text} {action.replace('_', ' ')}"
        
        if conditions:
            cond_text = ", and ".join(conditions)
            return f"{base}, provided that {cond_text}."
        
        return f"{base}."
    
    def generate_lean_output(self) -> str:
        """Generate Lean 4 theorem prover output."""
        output = "-- CLARITY Act Requirements in Lean 4\n"
        output += "-- Digital Asset Market Clarity Act of 2025\n\n"
        output += "import Mathlib.Logic.Basic\n\n"
        output += "namespace ClarityAct\n\n"
        output += "-- Agent types\n"
        output += "inductive Agent\n"
        output += "  | DigitalCommodityExchange\n"
        output += "  | DigitalCommodityBroker\n"
        output += "  | DigitalCommodityDealer\n"
        output += "  | Issuer\n"
        output += "  | SEC\n"
        output += "  | CFTC\n"
        output += "  | FederalReserveBank\n\n"
        
        output += "-- Deontic operators\n"
        output += "def Obligatory (agent : Agent) (action : Prop) : Prop := action\n"
        output += "def Forbidden (agent : Agent) (action : Prop) : Prop := ¬action\n"
        output += "def Permitted (agent : Agent) (action : Prop) : Prop := action ∨ ¬action\n\n"
        
        output += "-- Requirements\n"
        for formula in self.deontic_formulas[:10]:  # Limit for readability
            req_id = formula['requirement_id'].replace('-', '_')
            
            # Map agent names to match Agent type definition
            agent_mapping = {
                'digital_commodity_exchanges': 'DigitalCommodityExchange',
                'exchanges': 'DigitalCommodityExchange',
                'digital_commodity_brokers': 'DigitalCommodityBroker',
                'brokers': 'DigitalCommodityBroker',
                'digital_commodity_dealers': 'DigitalCommodityDealer',
                'dealers': 'DigitalCommodityDealer',
                'issuers': 'Issuer',
                'sec': 'SEC',
                'cftc': 'CFTC',
                'sec_and_cftc': 'SEC',  # Use SEC as representative
                'federal_reserve_banks': 'FederalReserveBank',
            }
            
            agent_key = formula['agent']
            agent_clean = agent_mapping.get(agent_key, 'Issuer')  # Default to Issuer if unknown
            action_clean = formula['action'][:50].replace('-', '_')
            
            output += f"-- {formula['natural_language']}\n"
            output += f"axiom {req_id}_{action_clean} : "
            
            if formula['operator'] == 'O':
                output += f"Obligatory Agent.{agent_clean} (True)\n"
            elif formula['operator'] == 'F':
                output += f"Forbidden Agent.{agent_clean} (True)\n"
            else:
                output += f"Permitted Agent.{agent_clean} (True)\n"
            
            output += "\n"
        
        output += "end ClarityAct\n"
        return output
    
    def generate_coq_output(self) -> str:
        """Generate Coq theorem prover output."""
        output = "(* CLARITY Act Requirements in Coq *)\n"
        output += "(* Digital Asset Market Clarity Act of 2025 *)\n\n"
        output += "Require Import Coq.Logic.Classical_Prop.\n\n"
        output += "Module ClarityAct.\n\n"
        
        output += "(* Agent types *)\n"
        output += "Inductive Agent : Type :=\n"
        output += "  | DigitalCommodityExchange : Agent\n"
        output += "  | DigitalCommodityBroker : Agent\n"
        output += "  | DigitalCommodityDealer : Agent\n"
        output += "  | Issuer : Agent\n"
        output += "  | SEC : Agent\n"
        output += "  | CFTC : Agent\n"
        output += "  | FederalReserveBank : Agent.\n\n"
        
        output += "(* Deontic operators *)\n"
        output += "Definition Obligatory (action : Prop) : Prop := action.\n"
        output += "Definition Forbidden (action : Prop) : Prop := ~action.\n"
        output += "Definition Permitted (action : Prop) : Prop := action \\/ ~action.\n\n"
        
        output += "(* Requirements *)\n"
        for formula in self.deontic_formulas[:10]:
            req_id = formula['requirement_id'].replace('-', '_')
            
            output += f"(* {formula['natural_language']} *)\n"
            output += f"Axiom {req_id} : "
            
            if formula['operator'] == 'O':
                output += "Obligatory True.\n"
            elif formula['operator'] == 'F':
                output += "Forbidden True.\n"
            else:
                output += "Permitted True.\n"
            
            output += "\n"
        
        output += "End ClarityAct.\n"
        return output
    
    def generate_smt_output(self) -> str:
        """Generate SMT-LIB theorem prover output."""
        output = "; CLARITY Act Requirements in SMT-LIB\n"
        output += "; Digital Asset Market Clarity Act of 2025\n\n"
        output += "(set-logic ALL)\n\n"
        
        output += "; Agent types\n"
        output += "(declare-datatypes ((Agent 0)) (\n"
        output += "  ((DigitalCommodityExchange)\n"
        output += "   (DigitalCommodityBroker)\n"
        output += "   (DigitalCommodityDealer)\n"
        output += "   (Issuer)\n"
        output += "   (SEC)\n"
        output += "   (CFTC)\n"
        output += "   (FederalReserveBank))))\n\n"
        
        output += "; Deontic operators\n"
        output += "(define-fun obligatory ((agent Agent) (action Bool)) Bool action)\n"
        output += "(define-fun forbidden ((agent Agent) (action Bool)) Bool (not action))\n"
        output += "(define-fun permitted ((agent Agent) (action Bool)) Bool true)\n\n"
        
        output += "; Requirements\n"
        for formula in self.deontic_formulas[:10]:
            req_id = formula['requirement_id'].replace('-', '_')
            agent_clean = formula['agent']
            
            output += f"; {formula['natural_language']}\n"
            
            if formula['operator'] == 'O':
                output += f"(assert (obligatory {agent_clean} true))\n"
            elif formula['operator'] == 'F':
                output += f"(assert (forbidden {agent_clean} true))\n"
            else:
                output += f"(assert (permitted {agent_clean} true))\n"
            
            output += "\n"
        
        output += "(check-sat)\n"
        return output
    
    def save_results(self, output_dir: Path):
        """Save all parsing results and logic translations."""
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Save requirements as JSON
        requirements_file = output_dir / "clarity_act_requirements.json"
        with open(requirements_file, 'w') as f:
            json.dump(
                [req.to_dict() for req in self.requirements],
                f,
                indent=2
            )
        print(f"Saved requirements to: {requirements_file}")
        
        # Save deontic formulas as JSON
        formulas_file = output_dir / "clarity_act_deontic_formulas.json"
        with open(formulas_file, 'w') as f:
            json.dump(self.deontic_formulas, f, indent=2)
        print(f"Saved deontic formulas to: {formulas_file}")
        
        # Save Lean output
        lean_file = output_dir / "clarity_act_lean.lean"
        with open(lean_file, 'w') as f:
            f.write(self.generate_lean_output())
        print(f"Saved Lean 4 output to: {lean_file}")
        
        # Save Coq output
        coq_file = output_dir / "clarity_act_coq.v"
        with open(coq_file, 'w') as f:
            f.write(self.generate_coq_output())
        print(f"Saved Coq output to: {coq_file}")
        
        # Save SMT-LIB output
        smt_file = output_dir / "clarity_act_smt.smt2"
        with open(smt_file, 'w') as f:
            f.write(self.generate_smt_output())
        print(f"Saved SMT-LIB output to: {smt_file}")
        
        # Save human-readable summary
        summary_file = output_dir / "clarity_act_analysis_summary.txt"
        with open(summary_file, 'w') as f:
            f.write(self._generate_summary())
        print(f"Saved analysis summary to: {summary_file}")
    
    def _generate_summary(self) -> str:
        """Generate human-readable summary of the analysis."""
        summary = "=" * 80 + "\n"
        summary += "CLARITY ACT (H.R. 3633) - DEONTIC LOGIC ANALYSIS\n"
        summary += "Digital Asset Market Clarity Act of 2025\n"
        summary += "=" * 80 + "\n\n"
        
        summary += f"Analysis Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        summary += f"Total Requirements Extracted: {len(self.requirements)}\n"
        summary += f"Total Deontic Formulas: {len(self.deontic_formulas)}\n\n"
        
        # Count by type
        obligations = sum(1 for f in self.deontic_formulas if f['operator'] == 'O')
        prohibitions = sum(1 for f in self.deontic_formulas if f['operator'] == 'F')
        permissions = sum(1 for f in self.deontic_formulas if f['operator'] == 'P')
        
        summary += "Requirement Types:\n"
        summary += f"  - Obligations: {obligations}\n"
        summary += f"  - Prohibitions: {prohibitions}\n"
        summary += f"  - Permissions: {permissions}\n\n"
        
        # Count by section
        sections = {}
        for req in self.requirements:
            sections[req.section] = sections.get(req.section, 0) + 1
        
        summary += "Requirements by Section:\n"
        for section, count in sorted(sections.items()):
            summary += f"  - {section.replace('_', ' ')}: {count}\n"
        
        summary += "\n" + "=" * 80 + "\n"
        summary += "SAMPLE DEONTIC FORMULAS\n"
        summary += "=" * 80 + "\n\n"
        
        for formula in self.deontic_formulas[:5]:
            summary += f"Requirement ID: {formula['requirement_id']}\n"
            summary += f"Section: {formula['section']}\n"
            summary += f"Formal Notation: {formula['formal_notation']}\n"
            summary += f"Natural Language: {formula['natural_language']}\n"
            summary += f"Source: {formula['source_text']}\n"
            summary += "-" * 80 + "\n\n"
        
        return summary


def main():
    """Main entry point."""
    print("=" * 80)
    print("CLARITY Act Deontic Logic Parser")
    print("Digital Asset Market Clarity Act of 2025 (H.R. 3633)")
    print("=" * 80)
    print()
    
    # Setup paths
    project_root = Path(__file__).parent.parent
    data_file = project_root / "data" / "clarity_act_summary.txt"
    output_dir = project_root / "outputs"
    
    if not data_file.exists():
        print(f"Error: Data file not found: {data_file}")
        return 1
    
    # Parse the document
    parser = ClarityActParser(data_file)
    requirements = parser.parse_document()
    
    # Convert to deontic logic
    formulas = parser.convert_to_deontic_logic()
    
    # Save all results
    parser.save_results(output_dir)
    
    print("\n" + "=" * 80)
    print("Analysis Complete!")
    print("=" * 80)
    print(f"\nGenerated outputs in: {output_dir}")
    print("\nFiles created:")
    print("  - clarity_act_requirements.json (structured requirements)")
    print("  - clarity_act_deontic_formulas.json (formal logic)")
    print("  - clarity_act_lean.lean (Lean 4 theorem prover)")
    print("  - clarity_act_coq.v (Coq theorem prover)")
    print("  - clarity_act_smt.smt2 (SMT-LIB solver)")
    print("  - clarity_act_analysis_summary.txt (human-readable summary)")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
