#!/usr/bin/env python3
"""
Simple usage example for the CLARITY Act Parser

This script demonstrates how to use the parser programmatically
to analyze specific requirements or sections.
"""

import sys
import json
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from clarity_act_parser import ClarityActParser


def main():
    """Demonstrate parser usage."""
    
    print("=" * 80)
    print("CLARITY Act Parser - Usage Example")
    print("=" * 80)
    print()
    
    # Initialize parser
    data_file = Path(__file__).parent / "data" / "clarity_act_summary.txt"
    parser = ClarityActParser(data_file)
    
    # Parse requirements
    print("1. Parsing CLARITY Act requirements...")
    requirements = parser.parse_document()
    print(f"   Found {len(requirements)} requirements\n")
    
    # Convert to deontic logic
    print("2. Converting to deontic logic...")
    formulas = parser.convert_to_deontic_logic()
    print(f"   Created {len(formulas)} deontic formulas\n")
    
    # Example 1: Show registration requirements
    print("3. Example: Registration Requirements")
    print("-" * 80)
    reg_requirements = [r for r in requirements if r.section == "REGISTRATION_AND_REPORTING"]
    for req in reg_requirements[:3]:
        print(f"   {req.requirement_id}: {req.text}")
    print()
    
    # Example 2: Show obligations by agent
    print("4. Example: Obligations by Agent")
    print("-" * 80)
    
    # Group by agent
    agents = {}
    for formula in formulas:
        if formula['operator'] == 'O':  # Obligations only
            agent = formula['agent']
            if agent not in agents:
                agents[agent] = []
            agents[agent].append(formula['action'])
    
    # Show top agents
    for agent, actions in list(agents.items())[:5]:
        print(f"   {agent.replace('_', ' ').title()}:")
        for action in actions[:2]:
            print(f"     - {action[:60]}")
        if len(actions) > 2:
            print(f"     - ... and {len(actions) - 2} more")
        print()
    
    # Example 3: Show prohibitions
    print("5. Example: Prohibitions (MUST NOT)")
    print("-" * 80)
    prohibitions = [f for f in formulas if f['operator'] == 'F']
    for prohibition in prohibitions:
        print(f"   {prohibition['requirement_id']}: {prohibition['natural_language']}")
    print()
    
    # Example 4: Show temporal constraints
    print("6. Example: Temporal Constraints")
    print("-" * 80)
    temporal_reqs = [r for r in requirements if r.temporal_constraint]
    for req in temporal_reqs[:3]:
        print(f"   {req.requirement_id}: {req.text}")
        print(f"   Deadline: {req.temporal_constraint}")
        print()
    
    # Example 5: Show formal notation
    print("7. Example: Formal Deontic Logic Notation")
    print("-" * 80)
    for formula in formulas[:5]:
        print(f"   {formula['formal_notation']}")
    print()
    
    # Example 6: Query specific requirement
    print("8. Example: Query Specific Requirement")
    print("-" * 80)
    req_id = "REG-001"
    req = next((r for r in requirements if r.requirement_id == req_id), None)
    if req:
        print(f"   Requirement ID: {req.requirement_id}")
        print(f"   Section: {req.section}")
        print(f"   Type: {req.requirement_type}")
        print(f"   Agent: {req.agent}")
        print(f"   Action: {req.action}")
        print(f"   Text: {req.text}")
    print()
    
    print("=" * 80)
    print("For complete analysis, run: python src/clarity_act_parser.py")
    print("=" * 80)


if __name__ == "__main__":
    main()
