#!/usr/bin/env python3
"""
Basic test suite for CLARITY Act parser

Validates that the parser correctly extracts and converts requirements.
"""

import sys
import json
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from clarity_act_parser import ClarityActParser, ClarityActRequirement


def test_parser_initialization():
    """Test that parser can be initialized."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    assert parser.document_path == data_file
    print("✓ Parser initialization works")


def test_requirement_extraction():
    """Test that requirements are extracted correctly."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    requirements = parser.parse_document()
    
    # Should extract 28 requirements
    assert len(requirements) == 28, f"Expected 28 requirements, got {len(requirements)}"
    
    # All should be ClarityActRequirement objects
    assert all(isinstance(r, ClarityActRequirement) for r in requirements)
    
    # All should have required fields
    for req in requirements:
        assert req.requirement_id
        assert req.section
        assert req.text
        assert req.agent
        assert req.action
    
    print(f"✓ Extracted {len(requirements)} requirements correctly")


def test_deontic_conversion():
    """Test that requirements convert to deontic logic."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    parser.parse_document()
    formulas = parser.convert_to_deontic_logic()
    
    # Should have same number of formulas as requirements
    assert len(formulas) == 28, f"Expected 28 formulas, got {len(formulas)}"
    
    # All should have required fields
    for formula in formulas:
        assert 'requirement_id' in formula
        assert 'operator' in formula
        assert 'agent' in formula
        assert 'action' in formula
        assert 'formal_notation' in formula
        assert 'natural_language' in formula
    
    print(f"✓ Converted {len(formulas)} deontic formulas correctly")


def test_operator_distribution():
    """Test that operators are distributed correctly."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    parser.parse_document()
    formulas = parser.convert_to_deontic_logic()
    
    obligations = sum(1 for f in formulas if f['operator'] == 'O')
    prohibitions = sum(1 for f in formulas if f['operator'] == 'F')
    permissions = sum(1 for f in formulas if f['operator'] == 'P')
    
    # Should have expected distribution
    assert obligations == 23, f"Expected 23 obligations, got {obligations}"
    assert prohibitions == 4, f"Expected 4 prohibitions, got {prohibitions}"
    assert permissions == 1, f"Expected 1 permission, got {permissions}"
    
    print(f"✓ Operator distribution correct: {obligations}O, {prohibitions}F, {permissions}P")


def test_section_distribution():
    """Test that sections are identified correctly."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    requirements = parser.parse_document()
    
    sections = {}
    for req in requirements:
        sections[req.section] = sections.get(req.section, 0) + 1
    
    # Should have 7 sections
    assert len(sections) == 7, f"Expected 7 sections, got {len(sections)}"
    
    # Check specific sections
    assert sections['REGISTRATION_AND_REPORTING'] == 6
    assert sections['TRADE_MARKET_INTEGRITY'] == 8
    assert sections['DECENTRALIZED_GOVERNANCE'] == 3
    assert sections['RULEMAKING_IMPLEMENTATION'] == 3
    assert sections['AML_BANK_SECRECY'] == 3
    assert sections['JURISDICTION'] == 3
    assert sections['FEDERAL_RESERVE_RESTRICTIONS'] == 2
    
    print(f"✓ Section distribution correct: {len(sections)} sections")


def test_agent_extraction():
    """Test that agents are extracted correctly."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    requirements = parser.parse_document()
    
    agents = set(req.agent for req in requirements)
    
    # Should extract various agents
    assert 'digital_commodity_exchanges' in agents or 'exchanges' in agents
    assert 'digital_commodity_brokers' in agents or 'brokers' in agents
    assert 'issuers' in agents
    assert 'sec' in agents or 'sec_and_cftc' in agents
    
    print(f"✓ Agent extraction correct: {len(agents)} unique agents")


def test_temporal_constraints():
    """Test that temporal constraints are extracted."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    requirements = parser.parse_document()
    
    temporal_reqs = [r for r in requirements if r.temporal_constraint]
    
    # Should have some temporal constraints
    assert len(temporal_reqs) >= 3, f"Expected at least 3 temporal constraints, got {len(temporal_reqs)}"
    
    # Check for 270 days constraint
    day_270_reqs = [r for r in temporal_reqs if '270 days' in str(r.temporal_constraint)]
    assert len(day_270_reqs) >= 2, "Should have at least 2 requirements with 270-day deadline"
    
    print(f"✓ Temporal constraint extraction correct: {len(temporal_reqs)} constraints")


def test_output_generation():
    """Test that all output formats can be generated."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    parser.parse_document()
    parser.convert_to_deontic_logic()
    
    # Generate all outputs
    lean_output = parser.generate_lean_output()
    coq_output = parser.generate_coq_output()
    smt_output = parser.generate_smt_output()
    
    # Verify outputs are non-empty and contain expected content
    assert len(lean_output) > 100
    assert 'namespace ClarityAct' in lean_output
    assert 'Obligatory' in lean_output
    
    assert len(coq_output) > 100
    assert 'Module ClarityAct' in coq_output
    assert 'Obligatory' in coq_output
    
    assert len(smt_output) > 100
    assert 'set-logic' in smt_output
    assert 'obligatory' in smt_output
    
    print("✓ All output formats generated correctly")


def test_json_serialization():
    """Test that results can be serialized to JSON."""
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    requirements = parser.parse_document()
    formulas = parser.convert_to_deontic_logic()
    
    # Test requirement serialization
    req_json = [r.to_dict() for r in requirements]
    json_str = json.dumps(req_json)
    assert len(json_str) > 100
    
    # Test formula serialization
    formula_json = json.dumps(formulas)
    assert len(formula_json) > 100
    
    print("✓ JSON serialization works correctly")


def run_all_tests():
    """Run all tests."""
    print("=" * 80)
    print("CLARITY Act Parser Test Suite")
    print("=" * 80)
    print()
    
    tests = [
        test_parser_initialization,
        test_requirement_extraction,
        test_deontic_conversion,
        test_operator_distribution,
        test_section_distribution,
        test_agent_extraction,
        test_temporal_constraints,
        test_output_generation,
        test_json_serialization
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__} failed: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__} error: {e}")
            failed += 1
    
    print()
    print("=" * 80)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("=" * 80)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
