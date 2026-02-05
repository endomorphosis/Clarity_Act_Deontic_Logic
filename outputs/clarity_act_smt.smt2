; CLARITY Act Requirements in SMT-LIB
; Digital Asset Market Clarity Act of 2025

(set-logic ALL)

; Agent sort and constants
(declare-sort Agent 0)
(declare-const agent_brokers Agent)
(declare-const agent_changes_in_control_or_governance Agent)
(declare-const agent_decentralized_blockchain_systems Agent)
(declare-const agent_denied_certifications Agent)
(declare-const agent_digital_asset_market_intermediaries Agent)
(declare-const agent_digital_commodity_brokers Agent)
(declare-const agent_digital_commodity_dealers Agent)
(declare-const agent_digital_commodity_exchanges Agent)
(declare-const agent_exchanges Agent)
(declare-const agent_expedited_registration_procedures Agent)
(declare-const agent_federal_reserve_banks Agent)
(declare-const agent_issuers Agent)
(declare-const agent_registered_entities Agent)
(declare-const agent_sec Agent)

; Deontic operators
(define-fun obligatory ((agent Agent) (action Bool)) Bool action)
(define-fun forbidden ((agent Agent) (action Bool)) Bool (not action))
(define-fun permitted ((agent Agent) (action Bool)) Bool true)

; Requirements
; The digital commodity exchanges is obligated to register with the cftc.
(assert (obligatory agent_digital_commodity_exchanges true))

; The digital commodity brokers is obligated to register with the cftc.
(assert (obligatory agent_digital_commodity_brokers true))

; The digital commodity dealers is obligated to register with the cftc.
(assert (obligatory agent_digital_commodity_dealers true))

; The issuers is obligated to disclose information about blockchain system maturity.
(assert (obligatory agent_issuers true))

; The issuers is obligated to disclose financial condition.
(assert (obligatory agent_issuers true))

; The sec is obligated to certify blockchain systems deemed mature.
(assert (obligatory agent_sec true))

; The exchanges is obligated to implement trade monitoring.
(assert (obligatory agent_exchanges true))

; The exchanges is obligated to maintain recordkeeping systems.
(assert (obligatory agent_exchanges true))

; The exchanges is forbidden from commingle customer assets.
(assert (forbidden agent_exchanges true))

; The brokers is obligated to implement risk management.
(assert (obligatory agent_brokers true))

; The brokers is obligated to maintain reporting duties.
(assert (obligatory agent_brokers true))

; The brokers is obligated to maintain capital obligations.
(assert (obligatory agent_brokers true))

; The exchanges is obligated to implement customer protection measures.
(assert (obligatory agent_exchanges true))

; The exchanges is obligated to implement custody rules, provided that federal or state supervision.
(assert (obligatory agent_exchanges true))

; The decentralized blockchain systems is forbidden from be treated as controlled.
(assert (forbidden agent_decentralized_blockchain_systems true))

; The changes in control or governance is obligated to updated certification or reporting.
(assert (obligatory agent_changes_in_control_or_governance true))

; The denied certifications is obligated to be, provided that public review.
(assert (obligatory agent_denied_certifications true))

; The sec is obligated to develop rules.
(assert (obligatory agent_sec true))

; The sec is obligated to issue rules.
(assert (obligatory agent_sec true))

; The expedited registration procedures is obligated to be available during transition.
(assert (obligatory agent_expedited_registration_procedures true))

; The digital asset market intermediaries is obligated to comply with bank secrecy act.
(assert (obligatory agent_digital_asset_market_intermediaries true))

; The registered entities is obligated to implement anti money laundering programs.
(assert (obligatory agent_registered_entities true))

; The registered entities is obligated to implement counter terrorism financing programs.
(assert (obligatory agent_registered_entities true))

; The sec is permitted to be exempt from sec registration.
(assert (permitted agent_sec true))

; The exchanges is obligated to sec maintains oversight for broker and dealer activities on national securities .
(assert (obligatory agent_exchanges true))

; The sec is obligated to sec maintains oversight for activities on alternative trading systems.
(assert (obligatory agent_sec true))

; The federal reserve banks is forbidden from offer central bank digital currencies directly to individuals.
(assert (forbidden agent_federal_reserve_banks true))

; The federal reserve banks is forbidden from use central bank digital currency for monetary policy operations.
(assert (forbidden agent_federal_reserve_banks true))

(check-sat)
