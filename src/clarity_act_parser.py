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
import argparse
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Dict, List, Any, Tuple
from datetime import datetime

# Add the repository root to the path so the bundled `ipfs_datasets_py/` package
# can be imported as `ipfs_datasets_py.*` when present.
sys.path.insert(0, str(Path(__file__).parent.parent))

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

        content = self._load_document_text(self.document_path)

        if self._looks_like_summary(content) and self.document_path.name.endswith("summary.txt"):
            self._parse_registration_requirements(content)
            self._parse_trade_integrity_requirements(content)
            self._parse_governance_requirements(content)
            self._parse_rulemaking_requirements(content)
            self._parse_aml_requirements(content)
            self._parse_jurisdiction_requirements(content)
            self._parse_federal_reserve_restrictions(content)
        else:
            self._parse_full_text_requirements(content)

        print(f"Extracted {len(self.requirements)} requirements")
        return self.requirements

    def _load_document_text(self, document_path: Path) -> str:
        suffix = document_path.suffix.lower()

        if suffix in {".txt", ".text"}:
            return document_path.read_text(errors="ignore")

        if suffix == ".xml":
            raw = document_path.read_text(errors="ignore")
            raw = re.sub(r"<!DOCTYPE[^>]*>\s*", "", raw, flags=re.IGNORECASE)
            try:
                root = ET.fromstring(raw)
            except ET.ParseError:
                cleaned_lines = [line for line in raw.splitlines() if not line.strip().upper().startswith("<!DOCTYPE")]
                root = ET.fromstring("\n".join(cleaned_lines))

            text_parts: List[str] = []
            for element_text in root.itertext():
                t = element_text.strip()
                if not t:
                    continue
                text_parts.append(t)
            return "\n".join(text_parts)

        if suffix == ".pdf":
            try:
                import pdfplumber  # type: ignore
            except Exception:
                raise RuntimeError("PDF parsing requested, but pdfplumber is not available")

            pages: List[str] = []
            with pdfplumber.open(str(document_path)) as pdf:
                for page in pdf.pages:
                    page_text = page.extract_text() or ""
                    if page_text.strip():
                        pages.append(page_text)
            return "\n\n".join(pages)

        return document_path.read_text(errors="ignore")

    def _looks_like_summary(self, content: str) -> bool:
        return "SUMMARY OF KEY REQUIREMENTS" in content.upper()

    def _parse_full_text_requirements(self, content: str):
        """Parse the full bill text and extract deontic (normative) statements."""

        current_section = "FULL_TEXT"
        requirement_counter = 0
        seen: set[str] = set()

        normalized = content.replace("\u2013", "-").replace("\u2014", "-")
        lines = [ln.strip() for ln in normalized.splitlines()]

        paragraphs: List[Tuple[str, str]] = []
        buffer: List[str] = []
        for line in lines:
            if not line:
                if buffer:
                    paragraphs.append((current_section, " ".join(buffer)))
                    buffer = []
                continue

            # Bill section headers typically use "SEC.". Avoid treating references like
            # "Section 5312" (U.S. Code amendments) as CLARITY Act section boundaries.
            section_match = re.match(r"^SEC\.\s*([0-9]{1,4})(?:\b|\.)", line, flags=re.IGNORECASE)
            # Congress bill XML commonly represents section numbers in <enum> nodes like "411.".
            enum_section_match = re.match(r"^([0-9]{1,4})\.\s*$", line)
            title_match = re.match(r"^TITLE\s+[IVXLC]+\b", line, flags=re.IGNORECASE)
            if section_match:
                if buffer:
                    paragraphs.append((current_section, " ".join(buffer)))
                    buffer = []
                current_section = f"SEC{section_match.group(1)}"
                continue
            if enum_section_match:
                if buffer:
                    paragraphs.append((current_section, " ".join(buffer)))
                    buffer = []
                current_section = f"SEC{enum_section_match.group(1)}"
                continue
            if title_match:
                if buffer:
                    paragraphs.append((current_section, " ".join(buffer)))
                    buffer = []
                current_section = title_match.group(0).strip().upper().replace(" ", "_")
                continue

            buffer.append(line)

        if buffer:
            paragraphs.append((current_section, " ".join(buffer)))

        for section, paragraph in paragraphs:
            for sentence in self._split_into_sentences(paragraph):
                sentence_clean = self._normalize_sentence(sentence)
                if not sentence_clean:
                    continue
                if not self._is_normative_sentence(sentence_clean):
                    continue
                fingerprint = re.sub(r"\s+", " ", sentence_clean.lower()).strip()
                if fingerprint in seen:
                    continue
                seen.add(fingerprint)

                requirement_counter += 1
                req_id = f"{section}-{requirement_counter:05d}"
                req = self._extract_requirement(sentence_clean, section, req_id)
                self.requirements.append(req)

    def _split_into_sentences(self, text: str) -> List[str]:
        text = re.sub(r"\s+", " ", text).strip()
        if not text:
            return []
        chunks = re.split(r"(?<=[\.;])\s+", text)
        return [c.strip() for c in chunks if c and c.strip()]

    def _normalize_sentence(self, sentence: str) -> str:
        sentence = sentence.strip()
        sentence = re.sub(r"\s+", " ", sentence)
        sentence = sentence.strip(" \t\r\n\u00a0")
        if len(sentence) < 12:
            return ""
        return sentence

    def _is_normative_sentence(self, sentence: str) -> bool:
        s = sentence.lower()

        # Exclude structural/boilerplate clauses that are technically modal but not
        # regulatory requirements.
        if re.search(r"\b(table of contents|short title)\b", s):
            return False
        if "may be cited as" in s:
            return False
        if "sense of congress" in s:
            return False
        if s.startswith("congress finds"):
            return False

        if re.search(r"\b(shall|must|may|required to|may not|shall not|must not)\b", s) is None and "unlawful" not in s:
            return False

        if re.search(r"\b(shall mean|means)\b", s):
            if "term" in s or "defined" in s:
                return False

        if re.search(r"\b(is amended|is redesignated|by striking|by inserting|by adding at the end)\b", s):
            return False

        return True
    
    def _extract_requirement(self, text: str, section: str, req_id: str) -> ClarityActRequirement:
        """Extract structured requirement from text."""
        
        lowered = text.lower()

        if re.search(r"\b(must not|shall not|may not)\b", lowered) or "unlawful" in lowered:
            req_type = "PROHIBITION"
        elif re.search(r"\b(may)\b", lowered):
            req_type = "PERMISSION"
        elif re.search(r"\b(must|shall|required to|requires|required)\b", lowered):
            req_type = "OBLIGATION"
        else:
            req_type = "OBLIGATION"
        
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
        unlawful_match = re.search(r"unlawful\s+for\s+(.+?)\s+to\s+", text, re.IGNORECASE)
        if unlawful_match:
            return self._normalize_identifier(unlawful_match.group(1))

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
            if re.search(rf"\b{re.escape(agent)}\b", text, flags=re.IGNORECASE):
                return agent.lower().replace(" ", "_")

        subject_match = re.match(r"^(.+?)\s+(shall\s+not|shall|must\s+not|must|may\s+not|may|required\s+to|requires?)\b", text, flags=re.IGNORECASE)
        if subject_match:
            candidate = subject_match.group(1)
            candidate = re.sub(r"^\(?[A-Za-z0-9]{1,4}\)?\s*[\).\-:]\s+", "", candidate)
            candidate = re.sub(r"^(except|unless|notwithstanding)\b.*?\,\s+", "", candidate, flags=re.IGNORECASE)
            candidate = re.sub(r"^(for\s+purposes\s+of|with\s+respect\s+to)\b.*?\,\s+", "", candidate, flags=re.IGNORECASE)
            return self._normalize_identifier(candidate)
        
        return "unspecified_agent"

    def _normalize_identifier(self, text: str) -> str:
        text = text.strip().strip("\"'“”‘’()").strip()
        text = re.sub(r"\s+", " ", text)
        words = text.split(" ")[:12]
        text = " ".join(words)
        text = re.sub(r"[^a-zA-Z0-9]+", "_", text).strip("_")
        text = re.sub(r"_+", "_", text)
        return text.lower() if text else "unspecified_agent"
    
    def _extract_action(self, text: str) -> str:
        """Extract the action that must/may be performed."""
        # Try to extract the verb phrase after MUST/SHALL/MAY
        patterns = [
            r"(?:MUST|SHALL|REQUIRE[DS]?|REQUIRED\s+TO)\s+(?:NOT\s+)?([^.]+?)(?:\s+(?:within|by|before|if|provided|subject|except)|\.|;|$)",
            r"MAY(?:\s+NOT)?\s+([^.]+?)(?:\s+(?:if|provided|subject|except)|\.|;|$)",
            r"unlawful\s+for\s+.+?\s+to\s+([^.]+?)(?:\.|;|$)"
        ]
        
        for pattern in patterns:
            match = re.search(pattern, text, re.IGNORECASE)
            if match:
                action = match.group(1).strip()
                # Clean up and normalize
                action = re.sub(r"\s+", " ", action)
                action = self._normalize_identifier(action)[:120]
                return action
        
        # Fallback: use a cleaned version of the text
        return self._normalize_identifier(text)[:80]
    
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
        action_clean = self._normalize_identifier(action)
        
        if conditions:
            # Format: O[agent]((condition1 ∧ condition2) → action)
            cond_str = " ∧ ".join([self._normalize_identifier(c)[:30] for c in conditions])
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
        output += "abbrev Agent := String\n\n"
        output += "-- Deontic operators\n"
        output += "def Obligatory (agent : Agent) (action : Prop) : Prop := action\n"
        output += "def Forbidden (agent : Agent) (action : Prop) : Prop := ¬action\n"
        output += "def Permitted (agent : Agent) (action : Prop) : Prop := action ∨ ¬action\n\n"

        output += "-- Requirements\n"
        for formula in self.deontic_formulas:
            req_id = self._normalize_identifier(formula['requirement_id']).upper()
            output += f"-- {formula['natural_language']}\n"
            output += f"axiom {req_id} : "
            if formula['operator'] == 'O':
                output += "Obligatory \"" + formula['agent'] + "\" (True)\n\n"
            elif formula['operator'] == 'F':
                output += "Forbidden \"" + formula['agent'] + "\" (True)\n\n"
            else:
                output += "Permitted \"" + formula['agent'] + "\" (True)\n\n"

        output += "end ClarityAct\n"
        return output
    
    def generate_coq_output(self) -> str:
        """Generate Coq theorem prover output."""
        output = "(* CLARITY Act Requirements in Coq *)\n"
        output += "(* Digital Asset Market Clarity Act of 2025 *)\n\n"
        output += "Require Import Coq.Logic.Classical_Prop.\n"
        output += "Require Import Coq.Strings.String.\n\n"
        output += "Module ClarityAct.\n\n"
        output += "Definition Agent := string.\n\n"
        
        output += "(* Deontic operators *)\n"
        output += "Definition Obligatory (_agent : Agent) (action : Prop) : Prop := action.\n"
        output += "Definition Forbidden (_agent : Agent) (action : Prop) : Prop := ~action.\n"
        output += "Definition Permitted (_agent : Agent) (action : Prop) : Prop := action \\/ ~action.\n\n"
        
        output += "(* Requirements *)\n"
        for formula in self.deontic_formulas:
            req_id = self._normalize_identifier(formula['requirement_id']).upper()
            output += f"(* {formula['natural_language']} *)\n"
            output += f"Axiom {req_id} : "
            if formula['operator'] == 'O':
                output += "Obligatory \"" + formula['agent'] + "\" True.\n\n"
            elif formula['operator'] == 'F':
                output += "Forbidden \"" + formula['agent'] + "\" True.\n\n"
            else:
                output += "Permitted \"" + formula['agent'] + "\" True.\n\n"
        
        output += "End ClarityAct.\n"
        return output
    
    def generate_smt_output(self) -> str:
        """Generate SMT-LIB theorem prover output."""
        output = "; CLARITY Act Requirements in SMT-LIB\n"
        output += "; Digital Asset Market Clarity Act of 2025\n\n"
        output += "(set-logic ALL)\n\n"

        output += "; Agent sort and constants\n"
        output += "(declare-sort Agent 0)\n"
        unique_agents = sorted({f['agent'] for f in self.deontic_formulas})
        agent_symbols: Dict[str, str] = {}
        for agent in unique_agents:
            sym = "agent_" + self._normalize_identifier(agent)
            if not sym:
                sym = "agent_unspecified"
            agent_symbols[agent] = sym
            output += f"(declare-const {sym} Agent)\n"
        output += "\n"

        output += "; Deontic operators\n"
        output += "(define-fun obligatory ((agent Agent) (action Bool)) Bool action)\n"
        output += "(define-fun forbidden ((agent Agent) (action Bool)) Bool (not action))\n"
        output += "(define-fun permitted ((agent Agent) (action Bool)) Bool true)\n\n"

        output += "; Requirements\n"
        for formula in self.deontic_formulas:
            agent_sym = agent_symbols.get(formula['agent'], "agent_unspecified")
            output += f"; {formula['natural_language']}\n"
            if formula['operator'] == 'O':
                output += f"(assert (obligatory {agent_sym} true))\n\n"
            elif formula['operator'] == 'F':
                output += f"(assert (forbidden {agent_sym} true))\n\n"
            else:
                output += f"(assert (permitted {agent_sym} true))\n\n"

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
    
    argp = argparse.ArgumentParser(description="Parse CLARITY Act text into deontic logic outputs")
    argp.add_argument(
        "input",
        nargs="?",
        default=None,
        help="Path to input document (.txt/.xml/.pdf). Defaults to data/clarity_act_summary.txt",
    )
    argp.add_argument(
        "--output-dir",
        default=None,
        help="Directory to write outputs (default: outputs/)",
    )
    args = argp.parse_args()

    project_root = Path(__file__).parent.parent
    data_file = Path(args.input) if args.input else (project_root / "data" / "clarity_act_summary.txt")
    output_dir = Path(args.output_dir) if args.output_dir else (project_root / "outputs")

    if not data_file.exists():
        print(f"Error: Input file not found: {data_file}")
        return 1

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
