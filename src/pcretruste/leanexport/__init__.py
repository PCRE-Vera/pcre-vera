"""Canonical emission of engine.tir.json and the hash tooling that pins it.

The Lean side reads the artifact through its own decoder, so nothing here is
part of the trusted base. Lands in M2 alongside the serializer.
"""
