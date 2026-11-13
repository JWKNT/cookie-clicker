#!/usr/bin/env python3
"""Build the Lean project and check proof placeholders and logical axioms."""

from pathlib import Path
import os
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
# Limit memory use during the full build. Keep an explicit caller setting.
os.environ.setdefault("LEAN_NUM_THREADS", "2")
if "--engine" not in sys.argv[1:]:
    sys.exit("The full audit requires the pinned native engine. Run: python3 lean/check.py --engine")
subprocess.run(["node", "tools/generate-completion-requirements.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-natural-route-partition.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-unicode13.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-timsort-ast.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-html-entities.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-browser-assets.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-browser-catalogue.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-css-properties.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-counter-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-lump-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-natural-season-formula.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-season-numeric-formula.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-godzamok-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-zero-time-cycle.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-production-frame.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-tiered-catalogue.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-textarea-host.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-canvas-host.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-loop-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-css-transform.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-css-layout.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-css-color.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-css-font.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-production-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-building-constructor-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-aura-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-gain-helpers-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-gains-loop-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/inventory-clock-sites.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-choice-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-css-border.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-prompt-layout.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-css-position.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-win-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-building-callback-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-achievement-count-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-notification-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-localization-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-seedrandom-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-seedrandom-mixkey-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-seedrandom-arc4-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-escape-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-orbs-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-reload-gate-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-cursor-cycle-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/generate-audio-source.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-canvas-observers.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-canvas-images.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-particle-effects.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run(["node", "tools/audit-sugar-yield.mjs", "--check"], cwd=root.parent, check=True)
if "--engine" in sys.argv[1:]:
    subprocess.run(["node", "tools/capture-game-assets.mjs", "--check-files"], cwd=root.parent, check=True)
    subprocess.run(["node", "tools/audit-building-cps.mjs", "--check"], cwd=root.parent, check=True)
    subprocess.run(["node", "tools/audit-timing-order.mjs", "--check"], cwd=root.parent, check=True)
    subprocess.run(["node", "tools/audit-orbs.mjs", "--check"], cwd=root.parent, check=True)
    subprocess.run(["node", "tools/audit-reload-gate.mjs", "--check"], cwd=root.parent, check=True)
subprocess.run([sys.executable, "generate_inventory.py", "--check"], cwd=root, check=True)
subprocess.run(["node", "check_rng_phase.mjs"], cwd=root, check=True)
for path in sorted(root.rglob("*.lean")):
    if ".lake" in path.relative_to(root).parts:
        continue
    text = path.read_text()
    match = re.search(r"\b(sorry|admit|axiom|native_decide)\b", text)
    if match:
        sys.exit(f"Forbidden proof token {match.group()} in {path.relative_to(root)}")

subprocess.run(["lake", "build"], cwd=root, check=True)
subprocess.run(["lake", "env", "lean", "--run", "check_media_autoplay.lean"], cwd=root, check=True)
subprocess.run(["node", "check_javascript_runtime_css.mjs"], cwd=root, check=True)
for script in ["check_js_number.mjs", "check_js_unicode.mjs", "check_js_encoding.mjs", "check_js_calendar.mjs", "check_js_date.mjs", "check_javascript_clock_value.mjs", "check_javascript_clock_source.mjs", "check_javascript_clock_loaders.mjs", "check_javascript_clock_calendar.mjs", "check_javascript_clock_gifts.mjs", "check_js_completion.mjs", "check_javascript_ast.mjs", "check_javascript_parser.mjs", "check_javascript_regexp.mjs", "check_javascript_eval.mjs", "check_javascript_sort.mjs", "check_javascript_seedrandom_capture.mjs"]:
    arguments = ["node", script]
    if "--engine" in sys.argv[1:]:
        arguments.append("--engine")
    subprocess.run(arguments, cwd=root, check=True)
if "--engine" in sys.argv[1:]:
    subprocess.run(["node", "check_javascript_clock_text.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_clock_text_codec.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_dom.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_browser.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_canvas.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_canvas_matrix.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_canvas_fill.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_canvas_deferred.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_canvas_image.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_textarea.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_geometry.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_metrics.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_border.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_background_position.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_css.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_css_opacity.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_font.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_color.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_width.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_height.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_transform.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_events.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "tools/audit-escape-input.mjs", "--check"], cwd=root.parent, check=True)
    subprocess.run(["node", "check_javascript_inline.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_input.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_mouse_dispatch.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_media_prefix.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_audio_muted.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_selection.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_focused_selection.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_focus.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_window_name.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_resources.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_storage.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_cookies.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_dynamic_function.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_functions.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_win.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_localization.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_lump_prefix.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_seedrandom_reset.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_seedrandom_entry.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_arc4.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_cursor_quotes.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_completion_monitor.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_garden_age.mjs", "--engine"], cwd=root, check=True)
    subprocess.run(["node", "check_javascript_console.mjs", "--engine"], cwd=root, check=True)
audit = subprocess.run(
    ["lake", "env", "lean", "Audit.lean"], cwd=root, check=True,
    capture_output=True, text=True,
)
print(audit.stdout, end="")
if audit.stderr:
    print(audit.stderr, end="", file=sys.stderr)
allowed = {"propext", "Classical.choice", "Quot.sound"}
reported = re.findall(r"depends on axioms: \[([^\]]*)\]", audit.stdout)
expected_reports = len(re.findall(r"^#print axioms ", (root / "Audit.lean").read_text(), re.MULTILINE))
report_count = len(reported) + len(re.findall(r"does not depend on any axioms", audit.stdout))
if report_count != expected_reports:
    sys.exit(f"Expected {expected_reports} axiom reports, received {report_count}")
for report in reported:
    axioms = {name.strip() for name in report.split(",") if name.strip()}
    if not axioms <= allowed:
        sys.exit(f"Unexpected axioms: {sorted(axioms - allowed)}")
print("Lean source and axiom checks passed.")
bridge_args = ["node", "check_completion.mjs"]
if "--engine" in sys.argv[1:]:
    bridge_args.append("--engine")
subprocess.run(bridge_args, cwd=root, check=True)
trace_args = ["node", "check_trace.mjs"]
if "--engine" in sys.argv[1:]:
    trace_args.append("--engine")
subprocess.run(trace_args, cwd=root, check=True)
garden_args = ["node", "check_garden.mjs"]
if "--engine" in sys.argv[1:]:
    garden_args.append("--engine")
subprocess.run(garden_args, cwd=root, check=True)
sugar_args = ["node", "check_sugar.mjs"]
if "--engine" in sys.argv[1:]:
    sugar_args.append("--engine")
subprocess.run(sugar_args, cwd=root, check=True)
policy_args = ["node", "check_policy_semantics.mjs"]
if "--engine" in sys.argv[1:]:
    policy_args.append("--engine")
subprocess.run(policy_args, cwd=root, check=True)
clock_args = ["node", "check_clock_model.mjs"]
if "--engine" in sys.argv[1:]:
    clock_args.append("--engine")
subprocess.run(clock_args, cwd=root, check=True)
rng_args = ["node", "check_rng.mjs"]
if "--engine" in sys.argv[1:]:
    rng_args.append("--engine")
subprocess.run(rng_args, cwd=root, check=True)
pet_args = ["node", "check_pet.mjs"]
if "--engine" in sys.argv[1:]:
    pet_args.append("--engine")
subprocess.run(pet_args, cwd=root, check=True)
market_args = ["node", "check_market.mjs"]
if "--engine" in sys.argv[1:]:
    market_args.append("--engine")
subprocess.run(market_args, cwd=root, check=True)

godzamok_args = ["node", "check_godzamok_rounding.mjs"]
if "--engine" in sys.argv[1:]:
    godzamok_args.append("--engine")
subprocess.run(godzamok_args, cwd=root, check=True)

startup_args = ["node", "check_startup_seed.mjs"]
if "--engine" in sys.argv[1:]:
    startup_args.append("--engine")
subprocess.run(startup_args, cwd=root, check=True)
