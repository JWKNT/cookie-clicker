/******/ (() => { // webpackBootstrap
/******/ 	var __webpack_modules__ = ({

/***/ 75:
/***/ (function(module) {

/**
 * jscolor - JavaScript Color Picker
 *
 * @link    http://jscolor.com
 * @license For open source use: GPLv3
 *          For commercial use: JSColor Commercial License
 * @author  Jan Odvarko - East Desire
 *
 * See usage examples at http://jscolor.com/examples/
 */


(function (global, factory) {

	'use strict';

	if ( true && typeof module.exports === 'object') {
		// Export jscolor as a module
		module.exports = global.document ?
			factory (global) :
			function (win) {
				if (!win.document) {
					throw new Error('jscolor needs a window with document');
				}
				return factory(win);
			}
		return;
	}

	// Default use (no module export)
	factory(global);

})(typeof window !== 'undefined' ? window : this, function (window) { // BEGIN factory

// BEGIN jscolor code


'use strict';


var jscolor = (function () { // BEGIN jscolor

var jsc = {


	initialized : false,

	instances : [], // created instances of jscolor

	readyQueue : [], // functions waiting to be called after init


	register : function () {
		if (typeof window !== 'undefined' && window.document) {
			if (window.document.readyState !== 'loading') {
				jsc.pub.init();
			} else {
				window.document.addEventListener('DOMContentLoaded', jsc.pub.init, false);
			}
		}
	},


	installBySelector : function (selector, rootNode) {
		rootNode = rootNode ? jsc.node(rootNode) : window.document;
		if (!rootNode) {
			throw new Error('Missing root node');
		}

		var elms = rootNode.querySelectorAll(selector);

		// for backward compatibility with DEPRECATED installation/configuration using className
		var matchClass = new RegExp('(^|\\s)(' + jsc.pub.lookupClass + ')(\\s*(\\{[^}]*\\})|\\s|$)', 'i');

		for (var i = 0; i < elms.length; i += 1) {

			if (elms[i].jscolor && elms[i].jscolor instanceof jsc.pub) {
				continue; // jscolor already installed on this element
			}

			if (elms[i].type !== undefined && elms[i].type.toLowerCase() == 'color' && jsc.isColorAttrSupported) {
				continue; // skips inputs of type 'color' if supported by the browser
			}

			var dataOpts, m;

			if (
				(dataOpts = jsc.getDataAttr(elms[i], 'jscolor')) !== null ||
				(elms[i].className && (m = elms[i].className.match(matchClass))) // installation using className (DEPRECATED)
			) {
				var targetElm = elms[i];

				var optsStr = '';
				if (dataOpts !== null) {
					optsStr = dataOpts;

				} else if (m) { // installation using className (DEPRECATED)
					console.warn('Installation using class name is DEPRECATED. Use data-jscolor="" attribute instead.' + jsc.docsRef);
					if (m[4]) {
						optsStr = m[4];
					}
				}

				var opts = null;
				if (optsStr.trim()) {
					try {
						opts = jsc.parseOptionsStr(optsStr);
					} catch (e) {
						console.warn(e + '\n' + optsStr);
					}
				}

				try {
					new jsc.pub(targetElm, opts);
				} catch (e) {
					console.warn(e);
				}
			}
		}
	},


	parseOptionsStr : function (str) {
		var opts = null;

		try {
			opts = JSON.parse(str);

		} catch (eParse) {
			if (!jsc.pub.looseJSON) {
				throw new Error('Could not parse jscolor options as JSON: ' + eParse);
			} else {
				// loose JSON syntax is enabled -> try to evaluate the options string as JavaScript object
				try {
					opts = (new Function ('var opts = (' + str + '); return typeof opts === "object" ? opts : {};'))();
				} catch (eEval) {
					throw new Error('Could not evaluate jscolor options: ' + eEval);
				}
			}
		}
		return opts;
	},


	getInstances : function () {
		var inst = [];
		for (var i = 0; i < jsc.instances.length; i += 1) {
			// if the targetElement still exists, the instance is considered "alive"
			if (jsc.instances[i] && jsc.instances[i].targetElement) {
				inst.push(jsc.instances[i]);
			}
		}
		return inst;
	},


	createEl : function (tagName) {
		var el = window.document.createElement(tagName);
		jsc.setData(el, 'gui', true);
		return el;
	},


	node : function (nodeOrSelector) {
		if (!nodeOrSelector) {
			return null;
		}

		if (typeof nodeOrSelector === 'string') {
			// query selector
			var sel = nodeOrSelector;
			var el = null;
			try {
				el = window.document.querySelector(sel);
			} catch (e) {
				console.warn(e);
				return null;
			}
			if (!el) {
				console.warn('No element matches the selector: %s', sel);
			}
			return el;
		}

		if (jsc.isNode(nodeOrSelector)) {
			// DOM node
			return nodeOrSelector;
		}

		console.warn('Invalid node of type %s: %s', typeof nodeOrSelector, nodeOrSelector);
		return null;
	},


	// See https://stackoverflow.com/questions/384286/
	isNode : function (val) {
		if (typeof Node === 'object') {
			return val instanceof Node;
		}
		return val && typeof val === 'object' && typeof val.nodeType === 'number' && typeof val.nodeName === 'string';
	},


	nodeName : function (node) {
		if (node && node.nodeName) {
			return node.nodeName.toLowerCase();
		}
		return false;
	},


	removeChildren : function (node) {
		while (node.firstChild) {
			node.removeChild(node.firstChild);
		}
	},


	isTextInput : function (el) {
		return el && jsc.nodeName(el) === 'input' && el.type.toLowerCase() === 'text';
	},


	isButton : function (el) {
		if (!el) {
			return false;
		}
		var n = jsc.nodeName(el);
		return (
			(n === 'button') ||
			(n === 'input' && ['button', 'submit', 'reset'].indexOf(el.type.toLowerCase()) > -1)
		);
	},


	isButtonEmpty : function (el) {
		switch (jsc.nodeName(el)) {
			case 'input': return (!el.value || el.value.trim() === '');
			case 'button': return (el.textContent.trim() === '');
		}
		return null; // could not determine element's text
	},


	// See https://github.com/WICG/EventListenerOptions/blob/gh-pages/explainer.md
	isPassiveEventSupported : (function () {
		var supported = false;

		try {
			var opts = Object.defineProperty({}, 'passive', {
				get: function () { supported = true; }
			});
			window.addEventListener('testPassive', null, opts);
			window.removeEventListener('testPassive', null, opts);
		} catch (e) {}

		return supported;
	})(),


	isColorAttrSupported : (function () {
		var elm = window.document.createElement('input');
		if (elm.setAttribute) {
			elm.setAttribute('type', 'color');
			if (elm.type.toLowerCase() == 'color') {
				return true;
			}
		}
		return false;
	})(),


	dataProp : '_data_jscolor',


	// usage:
	//   setData(obj, prop, value)
	//   setData(obj, {prop:value, ...})
	//
	setData : function () {
		var obj = arguments[0];

		if (arguments.length === 3) {
			// setting a single property
			var data = obj.hasOwnProperty(jsc.dataProp) ? obj[jsc.dataProp] : (obj[jsc.dataProp] = {});
			var prop = arguments[1];
			var value = arguments[2];

			data[prop] = value;
			return true;

		} else if (arguments.length === 2 && typeof arguments[1] === 'object') {
			// setting multiple properties
			var data = obj.hasOwnProperty(jsc.dataProp) ? obj[jsc.dataProp] : (obj[jsc.dataProp] = {});
			var map = arguments[1];

			for (var prop in map) {
				if (map.hasOwnProperty(prop)) {
					data[prop] = map[prop];
				}
			}
			return true;
		}

		throw new Error('Invalid arguments');
	},


	// usage:
	//   removeData(obj, prop, [prop...])
	//
	removeData : function () {
		var obj = arguments[0];
		if (!obj.hasOwnProperty(jsc.dataProp)) {
			return true; // data object does not exist
		}
		for (var i = 1; i < arguments.length; i += 1) {
			var prop = arguments[i];
			delete obj[jsc.dataProp][prop];
		}
		return true;
	},


	getData : function (obj, prop, setDefault) {
		if (!obj.hasOwnProperty(jsc.dataProp)) {
			// data object does not exist
			if (setDefault !== undefined) {
				obj[jsc.dataProp] = {}; // create data object
			} else {
				return undefined; // no value to return
			}
		}
		var data = obj[jsc.dataProp];

		if (!data.hasOwnProperty(prop) && setDefault !== undefined) {
			data[prop] = setDefault;
		}
		return data[prop];
	},


	getDataAttr : function (el, name) {
		var attrName = 'data-' + name;
		var attrValue = el.getAttribute(attrName);
		return attrValue;
	},


	setDataAttr : function (el, name, value) {
		var attrName = 'data-' + name;
		el.setAttribute(attrName, value);
	},


	_attachedGroupEvents : {},


	attachGroupEvent : function (groupName, el, evnt, func) {
		if (!jsc._attachedGroupEvents.hasOwnProperty(groupName)) {
			jsc._attachedGroupEvents[groupName] = [];
		}
		jsc._attachedGroupEvents[groupName].push([el, evnt, func]);
		el.addEventListener(evnt, func, false);
	},


	detachGroupEvents : function (groupName) {
		if (jsc._attachedGroupEvents.hasOwnProperty(groupName)) {
			for (var i = 0; i < jsc._attachedGroupEvents[groupName].length; i += 1) {
				var evt = jsc._attachedGroupEvents[groupName][i];
				evt[0].removeEventListener(evt[1], evt[2], false);
			}
			delete jsc._attachedGroupEvents[groupName];
		}
	},


	preventDefault : function (e) {
		if (e.preventDefault) { e.preventDefault(); }
		e.returnValue = false;
	},


	triggerEvent : function (el, eventName, bubbles, cancelable) {
		if (!el) {
			return;
		}

		var ev = null;

		if (typeof Event === 'function') {
			ev = new Event(eventName, {
				bubbles: bubbles,
				cancelable: cancelable
			});
		} else {
			// IE
			ev = window.document.createEvent('Event');
			ev.initEvent(eventName, bubbles, cancelable);
		}

		if (!ev) {
			return false;
		}

		// so that we know that the event was triggered internally
		jsc.setData(ev, 'internal', true);

		el.dispatchEvent(ev);
		return true;
	},


	triggerInputEvent : function (el, eventName, bubbles, cancelable) {
		if (!el) {
			return;
		}
		if (jsc.isTextInput(el)) {
			jsc.triggerEvent(el, eventName, bubbles, cancelable);
		}
	},


	eventKey : function (ev) {
		var keys = {
			9: 'Tab',
			13: 'Enter',
			27: 'Escape',
		};
		if (typeof ev.code === 'string') {
			return ev.code;
		} else if (ev.keyCode !== undefined && keys.hasOwnProperty(ev.keyCode)) {
			return keys[ev.keyCode];
		}
		return null;
	},


	strList : function (str) {
		if (!str) {
			return [];
		}
		return str.replace(/^\s+|\s+$/g, '').split(/\s+/);
	},


	// The className parameter (str) can only contain a single class name
	hasClass : function (elm, className) {
		if (!className) {
			return false;
		}
		if (elm.classList !== undefined) {
			return elm.classList.contains(className);
		}
		// polyfill
		return -1 != (' ' + elm.className.replace(/\s+/g, ' ') + ' ').indexOf(' ' + className + ' ');
	},


	// The className parameter (str) can contain multiple class names separated by whitespace
	addClass : function (elm, className) {
		var classNames = jsc.strList(className);

		if (elm.classList !== undefined) {
			for (var i = 0; i < classNames.length; i += 1) {
				elm.classList.add(classNames[i]);
			}
			return;
		}
		// polyfill
		for (var i = 0; i < classNames.length; i += 1) {
			if (!jsc.hasClass(elm, classNames[i])) {
				elm.className += (elm.className ? ' ' : '') + classNames[i];
			}
		}
	},


	// The className parameter (str) can contain multiple class names separated by whitespace
	removeClass : function (elm, className) {
		var classNames = jsc.strList(className);

		if (elm.classList !== undefined) {
			for (var i = 0; i < classNames.length; i += 1) {
				elm.classList.remove(classNames[i]);
			}
			return;
		}
		// polyfill
		for (var i = 0; i < classNames.length; i += 1) {
			var repl = new RegExp(
				'^\\s*' + classNames[i] + '\\s*|' +
				'\\s*' + classNames[i] + '\\s*$|' +
				'\\s+' + classNames[i] + '(\\s+)',
				'g'
			);
			elm.className = elm.className.replace(repl, '$1');
		}
	},


	getCompStyle : function (elm) {
		var compStyle = window.getComputedStyle ? window.getComputedStyle(elm) : elm.currentStyle;

		// Note: In Firefox, getComputedStyle returns null in a hidden iframe,
		// that's why we need to check if the returned value is non-empty
		if (!compStyle) {
			return {};
		}
		return compStyle;
	},


	// Note:
	//   Setting a property to NULL reverts it to the state before it was first set
	//   with the 'reversible' flag enabled
	//
	setStyle : function (elm, styles, important, reversible) {
		// using '' for standard priority (IE10 apparently doesn't like value undefined)
		var priority = important ? 'important' : '';
		var origStyle = null;

		for (var prop in styles) {
			if (styles.hasOwnProperty(prop)) {
				var setVal = null;

				if (styles[prop] === null) {
					// reverting a property value

					if (!origStyle) {
						// get the original style object, but dont't try to create it if it doesn't exist
						origStyle = jsc.getData(elm, 'origStyle');
					}
					if (origStyle && origStyle.hasOwnProperty(prop)) {
						// we have property's original value -> use it
						setVal = origStyle[prop];
					}

				} else {
					// setting a property value

					if (reversible) {
						if (!origStyle) {
							// get the original style object and if it doesn't exist, create it
							origStyle = jsc.getData(elm, 'origStyle', {});
						}
						if (!origStyle.hasOwnProperty(prop)) {
							// original property value not yet stored -> store it
							origStyle[prop] = elm.style[prop];
						}
					}
					setVal = styles[prop];
				}

				if (setVal !== null) {
					elm.style.setProperty(prop, setVal, priority);
				}
			}
		}
	},


	appendCss : function (css) {
		var head = document.querySelector('head');
		var style = document.createElement('style');
		style.innerText = css;
		head.appendChild(style);
	},


	appendDefaultCss : function (css) {
		jsc.appendCss(
			[
				'.jscolor-wrap, .jscolor-wrap div, .jscolor-wrap canvas { ' +
				'position:static; display:block; visibility:visible; overflow:visible; margin:0; padding:0; ' +
				'border:none; border-radius:0; outline:none; z-index:auto; float:none; ' +
				'width:auto; height:auto; left:auto; right:auto; top:auto; bottom:auto; min-width:0; min-height:0; max-width:none; max-height:none; ' +
				'background:none; clip:auto; opacity:1; transform:none; box-shadow:none; box-sizing:content-box; ' +
				'}',
				'.jscolor-wrap { clear:both; }',
				'.jscolor-wrap .jscolor-picker { position:relative; }',
				'.jscolor-wrap .jscolor-shadow { position:absolute; left:0; top:0; width:100%; height:100%; }',
				'.jscolor-wrap .jscolor-border { position:relative; }',
				'.jscolor-wrap .jscolor-palette { position:absolute; }',
				'.jscolor-wrap .jscolor-palette-sw { position:absolute; display:block; cursor:pointer; }',
				'.jscolor-wrap .jscolor-btn { position:absolute; overflow:hidden; white-space:nowrap; font:13px sans-serif; text-align:center; cursor:pointer; }',
			].join('\n')
		);
	},


	hexColor : function (r, g, b) {
		return '#' + (
			('0' + Math.round(r).toString(16)).slice(-2) +
			('0' + Math.round(g).toString(16)).slice(-2) +
			('0' + Math.round(b).toString(16)).slice(-2)
		).toUpperCase();
	},


	hexaColor : function (r, g, b, a) {
		return '#' + (
			('0' + Math.round(r).toString(16)).slice(-2) +
			('0' + Math.round(g).toString(16)).slice(-2) +
			('0' + Math.round(b).toString(16)).slice(-2) +
			('0' + Math.round(a * 255).toString(16)).slice(-2)
		).toUpperCase();
	},


	rgbColor : function (r, g, b) {
		return 'rgb(' +
			Math.round(r) + ',' +
			Math.round(g) + ',' +
			Math.round(b) +
		')';
	},


	rgbaColor : function (r, g, b, a) {
		return 'rgba(' +
			Math.round(r) + ',' +
			Math.round(g) + ',' +
			Math.round(b) + ',' +
			(Math.round((a===undefined || a===null ? 1 : a) * 100) / 100) +
		')';
	},


	linearGradient : (function () {

		function getFuncName () {
			var stdName = 'linear-gradient';
			var prefixes = ['', '-webkit-', '-moz-', '-o-', '-ms-'];
			var helper = window.document.createElement('div');

			for (var i = 0; i < prefixes.length; i += 1) {
				var tryFunc = prefixes[i] + stdName;
				var tryVal = tryFunc + '(to right, rgba(0,0,0,0), rgba(0,0,0,0))';

				helper.style.background = tryVal;
				if (helper.style.background) { // CSS background successfully set -> function name is supported
					return tryFunc;
				}
			}
			return stdName; // fallback to standard 'linear-gradient' without vendor prefix
		}

		var funcName = getFuncName();

		return function () {
			return funcName + '(' + Array.prototype.join.call(arguments, ', ') + ')';
		};

	})(),


	setBorderRadius : function (elm, value) {
		jsc.setStyle(elm, {'border-radius' : value || '0'});
	},


	setBoxShadow : function (elm, value) {
		jsc.setStyle(elm, {'box-shadow': value || 'none'});
	},


	getElementPos : function (e, relativeToViewport) {
		var x=0, y=0;
		var rect = e.getBoundingClientRect();
		x = rect.left;
		y = rect.top;
		if (!relativeToViewport) {
			var viewPos = jsc.getViewPos();
			x += viewPos[0];
			y += viewPos[1];
		}
		return [x, y];
	},


	getElementSize : function (e) {
		return [e.offsetWidth, e.offsetHeight];
	},


	// get pointer's X/Y coordinates relative to viewport
	getAbsPointerPos : function (e) {
		var x = 0, y = 0;
		if (typeof e.changedTouches !== 'undefined' && e.changedTouches.length) {
			// touch devices
			x = e.changedTouches[0].clientX;
			y = e.changedTouches[0].clientY;
		} else if (typeof e.clientX === 'number') {
			x = e.clientX;
			y = e.clientY;
		}
		return { x: x, y: y };
	},


	// get pointer's X/Y coordinates relative to target element
	getRelPointerPos : function (e) {
		var target = e.target || e.srcElement;
		var targetRect = target.getBoundingClientRect();

		var x = 0, y = 0;

		var clientX = 0, clientY = 0;
		if (typeof e.changedTouches !== 'undefined' && e.changedTouches.length) {
			// touch devices
			clientX = e.changedTouches[0].clientX;
			clientY = e.changedTouches[0].clientY;
		} else if (typeof e.clientX === 'number') {
			clientX = e.clientX;
			clientY = e.clientY;
		}

		x = clientX - targetRect.left;
		y = clientY - targetRect.top;
		return { x: x, y: y };
	},


	getViewPos : function () {
		var doc = window.document.documentElement;
		return [
			(window.pageXOffset || doc.scrollLeft) - (doc.clientLeft || 0),
			(window.pageYOffset || doc.scrollTop) - (doc.clientTop || 0)
		];
	},


	getViewSize : function () {
		var doc = window.document.documentElement;
		return [
			(window.innerWidth || doc.clientWidth),
			(window.innerHeight || doc.clientHeight),
		];
	},


	// r: 0-255
	// g: 0-255
	// b: 0-255
	//
	// returns: [ 0-360, 0-100, 0-100 ]
	//
	RGB_HSV : function (r, g, b) {
		r /= 255;
		g /= 255;
		b /= 255;
		var n = Math.min(Math.min(r,g),b);
		var v = Math.max(Math.max(r,g),b);
		var m = v - n;
		if (m === 0) { return [ null, 0, 100 * v ]; }
		var h = r===n ? 3+(b-g)/m : (g===n ? 5+(r-b)/m : 1+(g-r)/m);
		return [
			60 * (h===6?0:h),
			100 * (m/v),
			100 * v
		];
	},


	// h: 0-360
	// s: 0-100
	// v: 0-100
	//
	// returns: [ 0-255, 0-255, 0-255 ]
	//
	HSV_RGB : function (h, s, v) {
		var u = 255 * (v / 100);

		if (h === null) {
			return [ u, u, u ];
		}

		h /= 60;
		s /= 100;

		var i = Math.floor(h);
		var f = i%2 ? h-i : 1-(h-i);
		var m = u * (1 - s);
		var n = u * (1 - s * f);
		switch (i) {
			case 6:
			case 0: return [u,n,m];
			case 1: return [n,u,m];
			case 2: return [m,u,n];
			case 3: return [m,n,u];
			case 4: return [n,m,u];
			case 5: return [u,m,n];
		}
	},


	parseColorString : function (str) {
		var ret = {
			rgba: null,
			format: null // 'hex' | 'hexa' | 'rgb' | 'rgba'
		};

		var m;

		if (m = str.match(/^\W*([0-9A-F]{3,8})\W*$/i)) {
			// HEX notation

			if (m[1].length === 8) {
				// 8-char notation (= with alpha)
				ret.format = 'hexa';
				ret.rgba = [
					parseInt(m[1].slice(0,2),16),
					parseInt(m[1].slice(2,4),16),
					parseInt(m[1].slice(4,6),16),
					parseInt(m[1].slice(6,8),16) / 255
				];

			} else if (m[1].length === 6) {
				// 6-char notation
				ret.format = 'hex';
				ret.rgba = [
					parseInt(m[1].slice(0,2),16),
					parseInt(m[1].slice(2,4),16),
					parseInt(m[1].slice(4,6),16),
					null
				];

			} else if (m[1].length === 3) {
				// 3-char notation
				ret.format = 'hex';
				ret.rgba = [
					parseInt(m[1].charAt(0) + m[1].charAt(0),16),
					parseInt(m[1].charAt(1) + m[1].charAt(1),16),
					parseInt(m[1].charAt(2) + m[1].charAt(2),16),
					null
				];

			} else {
				return false;
			}

			return ret;
		}

		if (m = str.match(/^\W*rgba?\(([^)]*)\)\W*$/i)) {
			// rgb(...) or rgba(...) notation

			var par = m[1].split(',');
			var re = /^\s*(\d+|\d*\.\d+|\d+\.\d*)\s*$/;
			var mR, mG, mB, mA;
			if (
				par.length >= 3 &&
				(mR = par[0].match(re)) &&
				(mG = par[1].match(re)) &&
				(mB = par[2].match(re))
			) {
				ret.format = 'rgb';
				ret.rgba = [
					parseFloat(mR[1]) || 0,
					parseFloat(mG[1]) || 0,
					parseFloat(mB[1]) || 0,
					null
				];

				if (
					par.length >= 4 &&
					(mA = par[3].match(re))
				) {
					ret.format = 'rgba';
					ret.rgba[3] = parseFloat(mA[1]) || 0;
				}
				return ret;
			}
		}

		return false;
	},


	parsePaletteValue : function (mixed) {
		var vals = [];

		if (typeof mixed === 'string') { // input is a string of space separated color values
			// rgb() and rgba() may contain spaces too, so let's find all color values by regex
			mixed.replace(/#[0-9A-F]{3}\b|#[0-9A-F]{6}([0-9A-F]{2})?\b|rgba?\(([^)]*)\)/ig, function (val) {
				vals.push(val);
			});
		} else if (Array.isArray(mixed)) { // input is an array of color values
			vals = mixed;
		}

		// convert all values into uniform color format

		var colors = [];

		for (var i = 0; i < vals.length; i++) {
			var color = jsc.parseColorString(vals[i]);
			if (color) {
				colors.push(color);
			}
		}

		return colors;
	},


	containsTranparentColor : function (colors) {
		for (var i = 0; i < colors.length; i++) {
			var a = colors[i].rgba[3];
			if (a !== null && a < 1.0) {
				return true;
			}
		}
		return false;
	},


	isAlphaFormat : function (format) {
		switch (format.toLowerCase()) {
		case 'hexa':
		case 'rgba':
			return true;
		}
		return false;
	},


	// Canvas scaling for retina displays
	//
	// adapted from https://www.html5rocks.com/en/tutorials/canvas/hidpi/
	//
	scaleCanvasForHighDPR : function (canvas) {
		var dpr = window.devicePixelRatio || 1;
		canvas.width *= dpr;
		canvas.height *= dpr;
		var ctx = canvas.getContext('2d');
		ctx.scale(dpr, dpr);
	},


	genColorPreviewCanvas : function (color, separatorPos, specWidth, scaleForHighDPR) {

		var sepW = Math.round(jsc.pub.previewSeparator.length);
		var sqSize = jsc.pub.chessboardSize;
		var sqColor1 = jsc.pub.chessboardColor1;
		var sqColor2 = jsc.pub.chessboardColor2;

		var cWidth = specWidth ? specWidth : sqSize * 2;
		var cHeight = sqSize * 2;

		var canvas = jsc.createEl('canvas');
		var ctx = canvas.getContext('2d');

		canvas.width = cWidth;
		canvas.height = cHeight;
		if (scaleForHighDPR) {
			jsc.scaleCanvasForHighDPR(canvas);
		}

		// transparency chessboard - background
		ctx.fillStyle = sqColor1;
		ctx.fillRect(0, 0, cWidth, cHeight);

		// transparency chessboard - squares
		ctx.fillStyle = sqColor2;
		for (var x = 0; x < cWidth; x += sqSize * 2) {
			ctx.fillRect(x, 0, sqSize, sqSize);
			ctx.fillRect(x + sqSize, sqSize, sqSize, sqSize);
		}

		if (color) {
			// actual color in foreground
			ctx.fillStyle = color;
			ctx.fillRect(0, 0, cWidth, cHeight);
		}

		var start = null;
		switch (separatorPos) {
			case 'left':
				start = 0;
				ctx.clearRect(0, 0, sepW/2, cHeight);
				break;
			case 'right':
				start = cWidth - sepW;
				ctx.clearRect(cWidth - (sepW/2), 0, sepW/2, cHeight);
				break;
		}
		if (start !== null) {
			ctx.lineWidth = 1;
			for (var i = 0; i < jsc.pub.previewSeparator.length; i += 1) {
				ctx.beginPath();
				ctx.strokeStyle = jsc.pub.previewSeparator[i];
				ctx.moveTo(0.5 + start + i, 0);
				ctx.lineTo(0.5 + start + i, cHeight);
				ctx.stroke();
			}
		}

		return {
			canvas: canvas,
			width: cWidth,
			height: cHeight,
		};
	},


	// if position or width is not set => fill the entire element (0%-100%)
	genColorPreviewGradient : function (color, position, width) {
		var params = [];

		if (position && width) {
			params = [
				'to ' + {'left':'right', 'right':'left'}[position],
				color + ' 0%',
				color + ' ' + width + 'px',
				'rgba(0,0,0,0) ' + (width + 1) + 'px',
				'rgba(0,0,0,0) 100%',
			];
		} else {
			params = [
				'to right',
				color + ' 0%',
				color + ' 100%',
			];
		}

		return jsc.linearGradient.apply(this, params);
	},


	redrawPosition : function () {

		if (!jsc.picker || !jsc.picker.owner) {
			return; // picker is not shown
		}

		var thisObj = jsc.picker.owner;

		if (thisObj.container !== window.document.body) {

			jsc._drawPosition(thisObj, 0, 0, 'relative', false);

		} else {

			var tp, vp;

			if (thisObj.fixed) {
				// Fixed elements are positioned relative to viewport,
				// therefore we can ignore the scroll offset
				tp = jsc.getElementPos(thisObj.targetElement, true); // target pos
				vp = [0, 0]; // view pos
			} else {
				tp = jsc.getElementPos(thisObj.targetElement); // target pos
				vp = jsc.getViewPos(); // view pos
			}

			var ts = jsc.getElementSize(thisObj.targetElement); // target size
			var vs = jsc.getViewSize(); // view size
			var pd = jsc.getPickerDims(thisObj);
			var ps = [pd.borderW, pd.borderH]; // picker outer size
			var a, b, c;
			switch (thisObj.position.toLowerCase()) {
				case 'left': a=1; b=0; c=-1; break;
				case 'right':a=1; b=0; c=1; break;
				case 'top':  a=0; b=1; c=-1; break;
				default:     a=0; b=1; c=1; break;
			}
			var l = (ts[b]+ps[b])/2;

			// compute picker position
			if (!thisObj.smartPosition) {
				var pp = [
					tp[a],
					tp[b]+ts[b]-l+l*c
				];
			} else {
				var pp = [
					-vp[a]+tp[a]+ps[a] > vs[a] ?
						(-vp[a]+tp[a]+ts[a]/2 > vs[a]/2 && tp[a]+ts[a]-ps[a] >= 0 ? tp[a]+ts[a]-ps[a] : tp[a]) :
						tp[a],
					-vp[b]+tp[b]+ts[b]+ps[b]-l+l*c > vs[b] ?
						(-vp[b]+tp[b]+ts[b]/2 > vs[b]/2 && tp[b]+ts[b]-l-l*c >= 0 ? tp[b]+ts[b]-l-l*c : tp[b]+ts[b]-l+l*c) :
						(tp[b]+ts[b]-l+l*c >= 0 ? tp[b]+ts[b]-l+l*c : tp[b]+ts[b]-l-l*c)
				];
			}

			var x = pp[a];
			var y = pp[b];
			var positionValue = thisObj.fixed ? 'fixed' : 'absolute';
			var contractShadow =
				(pp[0] + ps[0] > tp[0] || pp[0] < tp[0] + ts[0]) &&
				(pp[1] + ps[1] < tp[1] + ts[1]);

			jsc._drawPosition(thisObj, x, y, positionValue, contractShadow);

		}

	},


	_drawPosition : function (thisObj, x, y, positionValue, contractShadow) {
		var vShadow = contractShadow ? 0 : thisObj.shadowBlur; // px

		jsc.picker.wrap.style.position = positionValue;

		if ( // To avoid unnecessary repositioning during scroll
			Math.round(parseFloat(jsc.picker.wrap.style.left)) !== Math.round(x) ||
			Math.round(parseFloat(jsc.picker.wrap.style.top)) !== Math.round(y)
		) {
			jsc.picker.wrap.style.left = x + 'px';
			jsc.picker.wrap.style.top = y + 'px';
		}

		jsc.setBoxShadow(
			jsc.picker.boxS,
			thisObj.shadow ?
				new jsc.BoxShadow(0, vShadow, thisObj.shadowBlur, 0, thisObj.shadowColor) :
				null);
	},


	getPickerDims : function (thisObj) {
		var w = 2 * thisObj.controlBorderWidth + thisObj.width;
		var h = 2 * thisObj.controlBorderWidth + thisObj.height;

		var sliderSpace = 2 * thisObj.controlBorderWidth + 2 * jsc.getControlPadding(thisObj) + thisObj.sliderSize;

		if (jsc.getSliderChannel(thisObj)) {
			w += sliderSpace;
		}
		if (thisObj.hasAlphaChannel()) {
			w += sliderSpace;
		}

		var pal = jsc.getPaletteDims(thisObj, w);

		if (pal.height) {
			h += pal.height + thisObj.padding;
		}
		if (thisObj.closeButton) {
			h += 2 * thisObj.controlBorderWidth + thisObj.padding + thisObj.buttonHeight;
		}

		var pW = w + (2 * thisObj.padding);
		var pH = h + (2 * thisObj.padding);

		return {
			contentW: w,
			contentH: h,
			paddedW: pW,
			paddedH: pH,
			borderW: pW + (2 * thisObj.borderWidth),
			borderH: pH + (2 * thisObj.borderWidth),
			palette: pal,
		};
	},


	getPaletteDims : function (thisObj, width) {
		var cols = 0, rows = 0, cellW = 0, cellH = 0, height = 0;
		var sampleCount = thisObj._palette ? thisObj._palette.length : 0;

		if (sampleCount) {
			cols = thisObj.paletteCols;
			rows = cols > 0 ? Math.ceil(sampleCount / cols) : 0;

			// color sample's dimensions (includes border)
			cellW = Math.max(1, Math.floor((width - ((cols - 1) * thisObj.paletteSpacing)) / cols));
			cellH = thisObj.paletteHeight ? Math.min(thisObj.paletteHeight, cellW) : cellW;
		}

		if (rows) {
			height =
				rows * cellH +
				(rows - 1) * thisObj.paletteSpacing;
		}

		return {
			cols: cols,
			rows: rows,
			cellW: cellW,
			cellH: cellH,
			width: width,
			height: height,
		};
	},


	getControlPadding : function (thisObj) {
		return Math.max(
			thisObj.padding / 2,
			(2 * thisObj.pointerBorderWidth + thisObj.pointerThickness) - thisObj.controlBorderWidth
		);
	},


	getPadYChannel : function (thisObj) {
		switch (thisObj.mode.charAt(1).toLowerCase()) {
			case 'v': return 'v'; break;
		}
		return 's';
	},


	getSliderChannel : function (thisObj) {
		if (thisObj.mode.length > 2) {
			switch (thisObj.mode.charAt(2).toLowerCase()) {
				case 's': return 's'; break;
				case 'v': return 'v'; break;
			}
		}
		return null;
	},


	// calls function specified in picker's property
	triggerCallback : function (thisObj, prop) {
		if (!thisObj[prop]) {
			return; // callback func not specified
		}
		var callback = null;

		if (typeof thisObj[prop] === 'string') {
			// string with code
			try {
				callback = new Function (thisObj[prop]);
			} catch (e) {
				console.error(e);
			}
		} else {
			// function
			callback = thisObj[prop];
		}

		if (callback) {
			callback.call(thisObj);
		}
	},


	// Triggers a color change related event(s) on all picker instances.
	// It is possible to specify multiple events separated with a space.
	triggerGlobal : function (eventNames) {
		var inst = jsc.getInstances();
		for (var i = 0; i < inst.length; i += 1) {
			inst[i].trigger(eventNames);
		}
	},


	_pointerMoveEvent : {
		mouse: 'mousemove',
		touch: 'touchmove'
	},
	_pointerEndEvent : {
		mouse: 'mouseup',
		touch: 'touchend'
	},


	_pointerOrigin : null,


	onDocumentKeyUp : function (e) {
		if (['Tab', 'Escape'].indexOf(jsc.eventKey(e)) !== -1) {
			if (jsc.picker && jsc.picker.owner) {
				jsc.picker.owner.tryHide();
			}
		}
	},


	onWindowResize : function (e) {
		jsc.redrawPosition();
	},


	onWindowScroll : function (e) {
		jsc.redrawPosition();
	},


	onParentScroll : function (e) {
		// hide the picker when one of the parent elements is scrolled
		if (jsc.picker && jsc.picker.owner) {
			jsc.picker.owner.tryHide();
		}
	},


	onDocumentMouseDown : function (e) {
		var target = e.target || e.srcElement;

		if (target.jscolor && target.jscolor instanceof jsc.pub) { // clicked targetElement -> show picker
			if (target.jscolor.showOnClick && !target.disabled) {
				target.jscolor.show();
			}
		} else if (jsc.getData(target, 'gui')) { // clicked jscolor's GUI element
			var control = jsc.getData(target, 'control');
			if (control) {
				// jscolor's control
				jsc.onControlPointerStart(e, target, jsc.getData(target, 'control'), 'mouse');
			}
		} else {
			// mouse is outside the picker's controls -> hide the color picker!
			if (jsc.picker && jsc.picker.owner) {
				jsc.picker.owner.tryHide();
			}
		}
	},


	onPickerTouchStart : function (e) {
		var target = e.target || e.srcElement;

		if (jsc.getData(target, 'control')) {
			jsc.onControlPointerStart(e, target, jsc.getData(target, 'control'), 'touch');
		}
	},


	onControlPointerStart : function (e, target, controlName, pointerType) {
		var thisObj = jsc.getData(target, 'instance');

		jsc.preventDefault(e);

		var registerDragEvents = function (doc, offset) {
			jsc.attachGroupEvent('drag', doc, jsc._pointerMoveEvent[pointerType],
				jsc.onDocumentPointerMove(e, target, controlName, pointerType, offset));
			jsc.attachGroupEvent('drag', doc, jsc._pointerEndEvent[pointerType],
				jsc.onDocumentPointerEnd(e, target, controlName, pointerType));
		};

		registerDragEvents(window.document, [0, 0]);

		if (window.parent && window.frameElement) {
			var rect = window.frameElement.getBoundingClientRect();
			var ofs = [-rect.left, -rect.top];
			registerDragEvents(window.parent.window.document, ofs);
		}

		var abs = jsc.getAbsPointerPos(e);
		var rel = jsc.getRelPointerPos(e);
		jsc._pointerOrigin = {
			x: abs.x - rel.x,
			y: abs.y - rel.y
		};

		switch (controlName) {
		case 'pad':
			// if the value slider is at the bottom, move it up
			if (jsc.getSliderChannel(thisObj) === 'v' && thisObj.channels.v === 0) {
				thisObj.fromHSVA(null, null, 100, null);
			}
			jsc.setPad(thisObj, e, 0, 0);
			break;

		case 'sld':
			jsc.setSld(thisObj, e, 0);
			break;

		case 'asld':
			jsc.setASld(thisObj, e, 0);
			break;
		}
		thisObj.trigger('input');
	},


	onDocumentPointerMove : function (e, target, controlName, pointerType, offset) {
		return function (e) {
			var thisObj = jsc.getData(target, 'instance');
			switch (controlName) {
			case 'pad':
				jsc.setPad(thisObj, e, offset[0], offset[1]);
				break;

			case 'sld':
				jsc.setSld(thisObj, e, offset[1]);
				break;

			case 'asld':
				jsc.setASld(thisObj, e, offset[1]);
				break;
			}
			thisObj.trigger('input');
		}
	},


	onDocumentPointerEnd : function (e, target, controlName, pointerType) {
		return function (e) {
			var thisObj = jsc.getData(target, 'instance');
			jsc.detachGroupEvents('drag');

			// Always trigger changes AFTER detaching outstanding mouse handlers,
			// in case some color change that occured in user-defined onChange/onInput handler
			// intruded into current mouse events
			thisObj.trigger('input');
			thisObj.trigger('change');
		};
	},


	onPaletteSampleClick : function (e) {
		var target = e.currentTarget;
		var thisObj = jsc.getData(target, 'instance');
		var color = jsc.getData(target, 'color');

		// when format is flexible, use the original format of this color sample
		if (thisObj.format.toLowerCase() === 'any') {
			thisObj._setFormat(color.format); // adapt format
			if (!jsc.isAlphaFormat(thisObj.getFormat())) {
				color.rgba[3] = 1.0; // when switching to a format that doesn't support alpha, set full opacity
			}
		}

		// if this color doesn't specify alpha, use alpha of 1.0 (if applicable)
		if (color.rgba[3] === null) {
			if (thisObj.paletteSetsAlpha === true || (thisObj.paletteSetsAlpha === 'auto' && thisObj._paletteHasTransparency)) {
				color.rgba[3] = 1.0;
			}
		}

		thisObj.fromRGBA.apply(thisObj, color.rgba);

		thisObj.trigger('input');
		thisObj.trigger('change');

		if (thisObj.hideOnPaletteClick) {
			thisObj.hide();
		}
	},


	setPad : function (thisObj, e, ofsX, ofsY) {
		var pointerAbs = jsc.getAbsPointerPos(e);
		var x = ofsX + pointerAbs.x - jsc._pointerOrigin.x - thisObj.padding - thisObj.controlBorderWidth;
		var y = ofsY + pointerAbs.y - jsc._pointerOrigin.y - thisObj.padding - thisObj.controlBorderWidth;

		var xVal = x * (360 / (thisObj.width - 1));
		var yVal = 100 - (y * (100 / (thisObj.height - 1)));

		switch (jsc.getPadYChannel(thisObj)) {
		case 's': thisObj.fromHSVA(xVal, yVal, null, null); break;
		case 'v': thisObj.fromHSVA(xVal, null, yVal, null); break;
		}
	},


	setSld : function (thisObj, e, ofsY) {
		var pointerAbs = jsc.getAbsPointerPos(e);
		var y = ofsY + pointerAbs.y - jsc._pointerOrigin.y - thisObj.padding - thisObj.controlBorderWidth;
		var yVal = 100 - (y * (100 / (thisObj.height - 1)));

		switch (jsc.getSliderChannel(thisObj)) {
		case 's': thisObj.fromHSVA(null, yVal, null, null); break;
		case 'v': thisObj.fromHSVA(null, null, yVal, null); break;
		}
	},


	setASld : function (thisObj, e, ofsY) {
		var pointerAbs = jsc.getAbsPointerPos(e);
		var y = ofsY + pointerAbs.y - jsc._pointerOrigin.y - thisObj.padding - thisObj.controlBorderWidth;
		var yVal = 1.0 - (y * (1.0 / (thisObj.height - 1)));

		if (yVal < 1.0) {
			// if format is flexible and the current format doesn't support alpha, switch to a suitable one
			var fmt = thisObj.getFormat();
			if (thisObj.format.toLowerCase() === 'any' && !jsc.isAlphaFormat(fmt)) {
				thisObj._setFormat(fmt === 'hex' ? 'hexa' : 'rgba');
			}
		}

		thisObj.fromHSVA(null, null, null, yVal);
	},


	createPadCanvas : function () {

		var ret = {
			elm: null,
			draw: null
		};

		var canvas = jsc.createEl('canvas');
		var ctx = canvas.getContext('2d');

		var drawFunc = function (width, height, type) {
			canvas.width = width;
			canvas.height = height;

			ctx.clearRect(0, 0, canvas.width, canvas.height);

			var hGrad = ctx.createLinearGradient(0, 0, canvas.width, 0);
			hGrad.addColorStop(0 / 6, '#F00');
			hGrad.addColorStop(1 / 6, '#FF0');
			hGrad.addColorStop(2 / 6, '#0F0');
			hGrad.addColorStop(3 / 6, '#0FF');
			hGrad.addColorStop(4 / 6, '#00F');
			hGrad.addColorStop(5 / 6, '#F0F');
			hGrad.addColorStop(6 / 6, '#F00');

			ctx.fillStyle = hGrad;
			ctx.fillRect(0, 0, canvas.width, canvas.height);

			var vGrad = ctx.createLinearGradient(0, 0, 0, canvas.height);
			switch (type.toLowerCase()) {
			case 's':
				vGrad.addColorStop(0, 'rgba(255,255,255,0)');
				vGrad.addColorStop(1, 'rgba(255,255,255,1)');
				break;
			case 'v':
				vGrad.addColorStop(0, 'rgba(0,0,0,0)');
				vGrad.addColorStop(1, 'rgba(0,0,0,1)');
				break;
			}
			ctx.fillStyle = vGrad;
			ctx.fillRect(0, 0, canvas.width, canvas.height);
		};

		ret.elm = canvas;
		ret.draw = drawFunc;

		return ret;
	},


	createSliderGradient : function () {

		var ret = {
			elm: null,
			draw: null
		};

		var canvas = jsc.createEl('canvas');
		var ctx = canvas.getContext('2d');

		var drawFunc = function (width, height, color1, color2) {
			canvas.width = width;
			canvas.height = height;

			ctx.clearRect(0, 0, canvas.width, canvas.height);

			var grad = ctx.createLinearGradient(0, 0, 0, canvas.height);
			grad.addColorStop(0, color1);
			grad.addColorStop(1, color2);

			ctx.fillStyle = grad;
			ctx.fillRect(0, 0, canvas.width, canvas.height);
		};

		ret.elm = canvas;
		ret.draw = drawFunc;

		return ret;
	},


	createASliderGradient : function () {

		var ret = {
			elm: null,
			draw: null
		};

		var canvas = jsc.createEl('canvas');
		var ctx = canvas.getContext('2d');

		var drawFunc = function (width, height, color) {
			canvas.width = width;
			canvas.height = height;

			ctx.clearRect(0, 0, canvas.width, canvas.height);

			var sqSize = canvas.width / 2;
			var sqColor1 = jsc.pub.chessboardColor1;
			var sqColor2 = jsc.pub.chessboardColor2;

			// dark gray background
			ctx.fillStyle = sqColor1;
			ctx.fillRect(0, 0, canvas.width, canvas.height);

			if (sqSize > 0) { // to avoid infinite loop
				for (var y = 0; y < canvas.height; y += sqSize * 2) {
					// light gray squares
					ctx.fillStyle = sqColor2;
					ctx.fillRect(0, y, sqSize, sqSize);
					ctx.fillRect(sqSize, y + sqSize, sqSize, sqSize);
				}
			}

			var grad = ctx.createLinearGradient(0, 0, 0, canvas.height);
			grad.addColorStop(0, color);
			grad.addColorStop(1, 'rgba(0,0,0,0)');

			ctx.fillStyle = grad;
			ctx.fillRect(0, 0, canvas.width, canvas.height);
		};

		ret.elm = canvas;
		ret.draw = drawFunc;

		return ret;
	},


	BoxShadow : (function () {
		var BoxShadow = function (hShadow, vShadow, blur, spread, color, inset) {
			this.hShadow = hShadow;
			this.vShadow = vShadow;
			this.blur = blur;
			this.spread = spread;
			this.color = color;
			this.inset = !!inset;
		};

		BoxShadow.prototype.toString = function () {
			var vals = [
				Math.round(this.hShadow) + 'px',
				Math.round(this.vShadow) + 'px',
				Math.round(this.blur) + 'px',
				Math.round(this.spread) + 'px',
				this.color
			];
			if (this.inset) {
				vals.push('inset');
			}
			return vals.join(' ');
		};

		return BoxShadow;
	})(),


	flags : {
		leaveValue : 1 << 0,
		leaveAlpha : 1 << 1,
		leavePreview : 1 << 2,
	},


	enumOpts : {
		format: ['auto', 'any', 'hex', 'hexa', 'rgb', 'rgba'],
		previewPosition: ['left', 'right'],
		mode: ['hsv', 'hvs', 'hs', 'hv'],
		position: ['left', 'right', 'top', 'bottom'],
		alphaChannel: ['auto', true, false],
		paletteSetsAlpha: ['auto', true, false],
	},


	deprecatedOpts : {
		// <old_option>: <new_option>  (<new_option> can be null)
		'styleElement': 'previewElement',
		'onFineChange': 'onInput',
		'overwriteImportant': 'forceStyle',
		'closable': 'closeButton',
		'insetWidth': 'controlBorderWidth',
		'insetColor': 'controlBorderColor',
		'refine': null,
	},


	docsRef : ' ' + 'See https://jscolor.com/docs/',


	//
	// Usage:
	// var myPicker = new JSColor(<targetElement> [, <options>])
	//
	// (constructor is accessible via both 'jscolor' and 'JSColor' name)
	//

	pub : function (targetElement, opts) {

		var THIS = this;

		if (!opts) {
			opts = {};
		}

		this.channels = {
			r: 255, // red [0-255]
			g: 255, // green [0-255]
			b: 255, // blue [0-255]
			h: 0, // hue [0-360]
			s: 0, // saturation [0-100]
			v: 100, // value (brightness) [0-100]
			a: 1.0, // alpha (opacity) [0.0 - 1.0]
		};

		// General options
		//
		this.format = 'auto'; // 'auto' | 'any' | 'hex' | 'hexa' | 'rgb' | 'rgba' - Format of the input/output value
		this.value = undefined; // INITIAL color value in any supported format. To change it later, use method fromString(), fromHSVA(), fromRGBA() or channel()
		this.alpha = undefined; // INITIAL alpha value. To change it later, call method channel('A', <value>)
		this.random = false; // whether to randomize the initial color. Either true | false, or an array of ranges: [minV, maxV, minS, maxS, minH, maxH, minA, maxA]
		this.onChange = undefined; // called when color changes. Value can be either a function or a string with JS code.
		this.onInput = undefined; // called repeatedly as the color is being changed, e.g. while dragging a slider. Value can be either a function or a string with JS code.
		this.valueElement = undefined; // element that will be used to display and input the color value
		this.alphaElement = undefined; // element that will be used to display and input the alpha (opacity) value
		this.previewElement = undefined; // element that will preview the picked color using CSS background
		this.previewPosition = 'left'; // 'left' | 'right' - position of the color preview in previewElement
		this.previewSize = 32; // (px) width of the color preview displayed in previewElement
		this.previewPadding = 8; // (px) space between color preview and content of the previewElement
		this.required = true; // whether the associated text input must always contain a color value. If false, the input can be left empty.
		this.hash = true; // whether to prefix the HEX color code with # symbol (only applicable for HEX format)
		this.uppercase = true; // whether to show the HEX color code in upper case (only applicable for HEX format)
		this.forceStyle = true; // whether to overwrite CSS style of the previewElement using !important flag

		// Color Picker options
		//
		this.width = 181; // width of the color spectrum (in px)
		this.height = 101; // height of the color spectrum (in px)
		this.mode = 'HSV'; // 'HSV' | 'HVS' | 'HS' | 'HV' - layout of the color picker controls
		this.alphaChannel = 'auto'; // 'auto' | true | false - if alpha channel is enabled, the alpha slider will be visible. If 'auto', it will be determined according to color format
		this.position = 'bottom'; // 'left' | 'right' | 'top' | 'bottom' - position relative to the target element
		this.smartPosition = true; // automatically change picker position when there is not enough space for it
		this.showOnClick = true; // whether to show the picker when user clicks its target element
		this.hideOnLeave = true; // whether to automatically hide the picker when user leaves its target element (e.g. upon clicking the document)
		this.palette = []; // colors to be displayed in the palette, specified as an array or a string of space separated color values (in any supported format)
		this.paletteCols = 10; // number of columns in the palette
		this.paletteSetsAlpha = 'auto'; // 'auto' | true | false - if true, palette colors that don't specify alpha will set alpha to 1.0
		this.paletteHeight = 16; // maximum height (px) of a row in the palette
		this.paletteSpacing = 4; // distance (px) between color samples in the palette
		this.hideOnPaletteClick = false; // when set to true, clicking the palette will also hide the color picker
		this.sliderSize = 16; // px
		this.crossSize = 8; // px
		this.closeButton = false; // whether to display the Close button
		this.closeText = 'Close';
		this.buttonColor = 'rgba(0,0,0,1)'; // CSS color
		this.buttonHeight = 18; // px
		this.padding = 12; // px
		this.backgroundColor = 'rgba(255,255,255,1)'; // CSS color
		this.borderWidth = 1; // px
		this.borderColor = 'rgba(187,187,187,1)'; // CSS color
		this.borderRadius = 8; // px
		this.controlBorderWidth = 1; // px
		this.controlBorderColor = 'rgba(187,187,187,1)'; // CSS color
		this.shadow = true; // whether to display a shadow
		this.shadowBlur = 15; // px
		this.shadowColor = 'rgba(0,0,0,0.2)'; // CSS color
		this.pointerColor = 'rgba(76,76,76,1)'; // CSS color
		this.pointerBorderWidth = 1; // px
		this.pointerBorderColor = 'rgba(255,255,255,1)'; // CSS color
		this.pointerThickness = 2; // px
		this.zIndex = 5000;
		this.container = undefined; // where to append the color picker (BODY element by default)

		// Experimental
		//
		this.minS = 0; // min allowed saturation (0 - 100)
		this.maxS = 100; // max allowed saturation (0 - 100)
		this.minV = 0; // min allowed value (brightness) (0 - 100)
		this.maxV = 100; // max allowed value (brightness) (0 - 100)
		this.minA = 0.0; // min allowed alpha (opacity) (0.0 - 1.0)
		this.maxA = 1.0; // max allowed alpha (opacity) (0.0 - 1.0)


		// Getter: option(name)
		// Setter: option(name, value)
		//         option({name:value, ...})
		//
		this.option = function () {
			if (!arguments.length) {
				throw new Error('No option specified');
			}

			if (arguments.length === 1 && typeof arguments[0] === 'string') {
				// getting a single option
				try {
					return getOption(arguments[0]);
				} catch (e) {
					console.warn(e);
				}
				return false;

			} else if (arguments.length >= 2 && typeof arguments[0] === 'string') {
				// setting a single option
				try {
					if (!setOption(arguments[0], arguments[1])) {
						return false;
					}
				} catch (e) {
					console.warn(e);
					return false;
				}
				this.redraw(); // immediately redraws the picker, if it's displayed
				this.exposeColor(); // in case some preview-related or format-related option was changed
				return true;

			} else if (arguments.length === 1 && typeof arguments[0] === 'object') {
				// setting multiple options
				var opts = arguments[0];
				var success = true;
				for (var opt in opts) {
					if (opts.hasOwnProperty(opt)) {
						try {
							if (!setOption(opt, opts[opt])) {
								success = false;
							}
						} catch (e) {
							console.warn(e);
							success = false;
						}
					}
				}
				this.redraw(); // immediately redraws the picker, if it's displayed
				this.exposeColor(); // in case some preview-related or format-related option was changed
				return success;
			}

			throw new Error('Invalid arguments');
		}


		// Getter: channel(name)
		// Setter: channel(name, value)
		//
		this.channel = function (name, value) {
			if (typeof name !== 'string') {
				throw new Error('Invalid value for channel name: ' + name);
			}

			if (value === undefined) {
				// getting channel value
				if (!this.channels.hasOwnProperty(name.toLowerCase())) {
					console.warn('Getting unknown channel: ' + name);
					return false;
				}
				return this.channels[name.toLowerCase()];

			} else {
				// setting channel value
				var res = false;
				switch (name.toLowerCase()) {
					case 'r': res = this.fromRGBA(value, null, null, null); break;
					case 'g': res = this.fromRGBA(null, value, null, null); break;
					case 'b': res = this.fromRGBA(null, null, value, null); break;
					case 'h': res = this.fromHSVA(value, null, null, null); break;
					case 's': res = this.fromHSVA(null, value, null, null); break;
					case 'v': res = this.fromHSVA(null, null, value, null); break;
					case 'a': res = this.fromHSVA(null, null, null, value); break;
					default:
						console.warn('Setting unknown channel: ' + name);
						return false;
				}
				if (res) {
					this.redraw(); // immediately redraws the picker, if it's displayed
					return true;
				}
			}

			return false;
		}


		// Triggers given input event(s) by:
		// - executing on<Event> callback specified as picker's option
		// - triggering standard DOM event listeners attached to the value element
		//
		// It is possible to specify multiple events separated with a space.
		//
		this.trigger = function (eventNames) {
			var evs = jsc.strList(eventNames);
			for (var i = 0; i < evs.length; i += 1) {
				var ev = evs[i].toLowerCase();

				// trigger a callback
				var callbackProp = null;
				switch (ev) {
					case 'input': callbackProp = 'onInput'; break;
					case 'change': callbackProp = 'onChange'; break;
				}
				if (callbackProp) {
					jsc.triggerCallback(this, callbackProp);
				}

				// trigger standard DOM event listeners on the value element
				jsc.triggerInputEvent(this.valueElement, ev, true, true);
			}
		};


		// h: 0-360
		// s: 0-100
		// v: 0-100
		// a: 0.0-1.0
		//
		this.fromHSVA = function (h, s, v, a, flags) { // null = don't change
			if (h === undefined) { h = null; }
			if (s === undefined) { s = null; }
			if (v === undefined) { v = null; }
			if (a === undefined) { a = null; }

			if (h !== null) {
				if (isNaN(h)) { return false; }
				this.channels.h = Math.max(0, Math.min(360, h));
			}
			if (s !== null) {
				if (isNaN(s)) { return false; }
				this.channels.s = Math.max(0, Math.min(100, this.maxS, s), this.minS);
			}
			if (v !== null) {
				if (isNaN(v)) { return false; }
				this.channels.v = Math.max(0, Math.min(100, this.maxV, v), this.minV);
			}
			if (a !== null) {
				if (isNaN(a)) { return false; }
				this.channels.a = this.hasAlphaChannel() ?
					Math.max(0, Math.min(1, this.maxA, a), this.minA) :
					1.0; // if alpha channel is disabled, the color should stay 100% opaque
			}

			var rgb = jsc.HSV_RGB(
				this.channels.h,
				this.channels.s,
				this.channels.v
			);
			this.channels.r = rgb[0];
			this.channels.g = rgb[1];
			this.channels.b = rgb[2];

			this.exposeColor(flags);
			return true;
		};


		// r: 0-255
		// g: 0-255
		// b: 0-255
		// a: 0.0-1.0
		//
		this.fromRGBA = function (r, g, b, a, flags) { // null = don't change
			if (r === undefined) { r = null; }
			if (g === undefined) { g = null; }
			if (b === undefined) { b = null; }
			if (a === undefined) { a = null; }

			if (r !== null) {
				if (isNaN(r)) { return false; }
				r = Math.max(0, Math.min(255, r));
			}
			if (g !== null) {
				if (isNaN(g)) { return false; }
				g = Math.max(0, Math.min(255, g));
			}
			if (b !== null) {
				if (isNaN(b)) { return false; }
				b = Math.max(0, Math.min(255, b));
			}
			if (a !== null) {
				if (isNaN(a)) { return false; }
				this.channels.a = this.hasAlphaChannel() ?
					Math.max(0, Math.min(1, this.maxA, a), this.minA) :
					1.0; // if alpha channel is disabled, the color should stay 100% opaque
			}

			var hsv = jsc.RGB_HSV(
				r===null ? this.channels.r : r,
				g===null ? this.channels.g : g,
				b===null ? this.channels.b : b
			);
			if (hsv[0] !== null) {
				this.channels.h = Math.max(0, Math.min(360, hsv[0]));
			}
			if (hsv[2] !== 0) { // fully black color stays black through entire saturation range, so let's not change saturation
				this.channels.s = Math.max(0, this.minS, Math.min(100, this.maxS, hsv[1]));
			}
			this.channels.v = Math.max(0, this.minV, Math.min(100, this.maxV, hsv[2]));

			// update RGB according to final HSV, as some values might be trimmed
			var rgb = jsc.HSV_RGB(this.channels.h, this.channels.s, this.channels.v);
			this.channels.r = rgb[0];
			this.channels.g = rgb[1];
			this.channels.b = rgb[2];

			this.exposeColor(flags);
			return true;
		};


		// DEPRECATED. Use .fromHSVA() instead
		//
		this.fromHSV = function (h, s, v, flags) {
			console.warn('fromHSV() method is DEPRECATED. Using fromHSVA() instead.' + jsc.docsRef);
			return this.fromHSVA(h, s, v, null, flags);
		};


		// DEPRECATED. Use .fromRGBA() instead
		//
		this.fromRGB = function (r, g, b, flags) {
			console.warn('fromRGB() method is DEPRECATED. Using fromRGBA() instead.' + jsc.docsRef);
			return this.fromRGBA(r, g, b, null, flags);
		};


		this.fromString = function (str, flags) {
			if (!this.required && str.trim() === '') {
				// setting empty string to an optional color input
				this.setPreviewElementBg(null);
				this.setValueElementValue('');
				return true;
			}

			var color = jsc.parseColorString(str);
			if (!color) {
				return false; // could not parse
			}
			if (this.format.toLowerCase() === 'any') {
				this._setFormat(color.format); // adapt format
				if (!jsc.isAlphaFormat(this.getFormat())) {
					color.rgba[3] = 1.0; // when switching to a format that doesn't support alpha, set full opacity
				}
			}
			this.fromRGBA(
				color.rgba[0],
				color.rgba[1],
				color.rgba[2],
				color.rgba[3],
				flags
			);
			return true;
		};


		this.randomize = function (minV, maxV, minS, maxS, minH, maxH, minA, maxA) {
			if (minV === undefined) { minV = 0; }
			if (maxV === undefined) { maxV = 100; }
			if (minS === undefined) { minS = 0; }
			if (maxS === undefined) { maxS = 100; }
			if (minH === undefined) { minH = 0; }
			if (maxH === undefined) { maxH = 359; }
			if (minA === undefined) { minA = 1; }
			if (maxA === undefined) { maxA = 1; }

			this.fromHSVA(
				minH + Math.floor(Math.random() * (maxH - minH + 1)),
				minS + Math.floor(Math.random() * (maxS - minS + 1)),
				minV + Math.floor(Math.random() * (maxV - minV + 1)),
				((100 * minA) + Math.floor(Math.random() * (100 * (maxA - minA) + 1))) / 100
			);
		};


		this.toString = function (format) {
			if (format === undefined) {
				format = this.getFormat(); // format not specified -> use the current format
			}
			switch (format.toLowerCase()) {
				case 'hex': return this.toHEXString(); break;
				case 'hexa': return this.toHEXAString(); break;
				case 'rgb': return this.toRGBString(); break;
				case 'rgba': return this.toRGBAString(); break;
			}
			return false;
		};


		this.toHEXString = function () {
			return jsc.hexColor(
				this.channels.r,
				this.channels.g,
				this.channels.b
			);
		};


		this.toHEXAString = function () {
			return jsc.hexaColor(
				this.channels.r,
				this.channels.g,
				this.channels.b,
				this.channels.a
			);
		};


		this.toRGBString = function () {
			return jsc.rgbColor(
				this.channels.r,
				this.channels.g,
				this.channels.b
			);
		};


		this.toRGBAString = function () {
			return jsc.rgbaColor(
				this.channels.r,
				this.channels.g,
				this.channels.b,
				this.channels.a
			);
		};


		this.toGrayscale = function () {
			return (
				0.213 * this.channels.r +
				0.715 * this.channels.g +
				0.072 * this.channels.b
			);
		};


		this.toCanvas = function () {
			return jsc.genColorPreviewCanvas(this.toRGBAString()).canvas;
		};


		this.toDataURL = function () {
			return this.toCanvas().toDataURL();
		};


		this.toBackground = function () {
			return jsc.pub.background(this.toRGBAString());
		};


		this.isLight = function () {
			return this.toGrayscale() > 255 / 2;
		};


		this.hide = function () {
			if (isPickerOwner()) {
				detachPicker();
			}
		};


		this.show = function () {
			drawPicker();
		};


		this.redraw = function () {
			if (isPickerOwner()) {
				drawPicker();
			}
		};


		this.getFormat = function () {
			return this._currentFormat;
		};


		this._setFormat = function (format) {
			this._currentFormat = format.toLowerCase();
		};


		this.hasAlphaChannel = function () {
			if (this.alphaChannel === 'auto') {
				return (
					this.format.toLowerCase() === 'any' || // format can change on the fly (e.g. from hex to rgba), so let's consider the alpha channel enabled
					jsc.isAlphaFormat(this.getFormat()) || // the current format supports alpha channel
					this.alpha !== undefined || // initial alpha value is set, so we're working with alpha channel
					this.alphaElement !== undefined // the alpha value is redirected, so we're working with alpha channel
				);
			}

			return this.alphaChannel; // the alpha channel is explicitly set
		};


		this.processValueInput = function (str) {
			if (!this.fromString(str)) {
				// could not parse the color value - let's just expose the current color
				this.exposeColor();
			}
		};


		this.processAlphaInput = function (str) {
			if (!this.fromHSVA(null, null, null, parseFloat(str))) {
				// could not parse the alpha value - let's just expose the current color
				this.exposeColor();
			}
		};


		this.exposeColor = function (flags) {
			var colorStr = this.toString();
			var fmt = this.getFormat();

			// reflect current color in data- attribute
			jsc.setDataAttr(this.targetElement, 'current-color', colorStr);

			if (!(flags & jsc.flags.leaveValue) && this.valueElement) {
				if (fmt === 'hex' || fmt === 'hexa') {
					if (!this.uppercase) { colorStr = colorStr.toLowerCase(); }
					if (!this.hash) { colorStr = colorStr.replace(/^#/, ''); }
				}
				this.setValueElementValue(colorStr);
			}

			if (!(flags & jsc.flags.leaveAlpha) && this.alphaElement) {
				var alphaVal = Math.round(this.channels.a * 100) / 100;
				this.setAlphaElementValue(alphaVal);
			}

			if (!(flags & jsc.flags.leavePreview) && this.previewElement) {
				var previewPos = null; // 'left' | 'right' (null -> fill the entire element)

				if (
					jsc.isTextInput(this.previewElement) || // text input
					(jsc.isButton(this.previewElement) && !jsc.isButtonEmpty(this.previewElement)) // button with text
				) {
					previewPos = this.previewPosition;
				}

				this.setPreviewElementBg(this.toRGBAString());
			}

			if (isPickerOwner()) {
				redrawPad();
				redrawSld();
				redrawASld();
			}
		};


		this.setPreviewElementBg = function (color) {
			if (!this.previewElement) {
				return;
			}

			var position = null; // color preview position:  null | 'left' | 'right'
			var width = null; // color preview width:  px | null = fill the entire element
			if (
				jsc.isTextInput(this.previewElement) || // text input
				(jsc.isButton(this.previewElement) && !jsc.isButtonEmpty(this.previewElement)) // button with text
			) {
				position = this.previewPosition;
				width = this.previewSize;
			}

			var backgrounds = [];

			if (!color) {
				// there is no color preview to display -> let's remove any previous background image
				backgrounds.push({
					image: 'none',
					position: 'left top',
					size: 'auto',
					repeat: 'no-repeat',
					origin: 'padding-box',
				});
			} else {
				// CSS gradient for background color preview
				backgrounds.push({
					image: jsc.genColorPreviewGradient(
						color,
						position,
						width ? width - jsc.pub.previewSeparator.length : null
					),
					position: 'left top',
					size: 'auto',
					repeat: position ? 'repeat-y' : 'repeat',
					origin: 'padding-box',
				});

				// data URL of generated PNG image with a gray transparency chessboard
				var preview = jsc.genColorPreviewCanvas(
					'rgba(0,0,0,0)',
					position ? {'left':'right', 'right':'left'}[position] : null,
					width,
					true
				);
				backgrounds.push({
					image: 'url(\'' + preview.canvas.toDataURL() + '\')',
					position: (position || 'left') + ' top',
					size: preview.width + 'px ' + preview.height + 'px',
					repeat: position ? 'repeat-y' : 'repeat',
					origin: 'padding-box',
				});
			}

			var bg = {
				image: [],
				position: [],
				size: [],
				repeat: [],
				origin: [],
			};
			for (var i = 0; i < backgrounds.length; i += 1) {
				bg.image.push(backgrounds[i].image);
				bg.position.push(backgrounds[i].position);
				bg.size.push(backgrounds[i].size);
				bg.repeat.push(backgrounds[i].repeat);
				bg.origin.push(backgrounds[i].origin);
			}

			// set previewElement's background-images
			var sty = {
				'background-image': bg.image.join(', '),
				'background-position': bg.position.join(', '),
				'background-size': bg.size.join(', '),
				'background-repeat': bg.repeat.join(', '),
				'background-origin': bg.origin.join(', '),
			};
			jsc.setStyle(this.previewElement, sty, this.forceStyle);


			// set/restore previewElement's padding
			var padding = {
				left: null,
				right: null,
			};
			if (position) {
				padding[position] = (this.previewSize + this.previewPadding) + 'px';
			}

			var sty = {
				'padding-left': padding.left,
				'padding-right': padding.right,
			};
			jsc.setStyle(this.previewElement, sty, this.forceStyle, true);
		};


		this.setValueElementValue = function (str) {
			if (this.valueElement) {
				if (jsc.nodeName(this.valueElement) === 'input') {
					this.valueElement.value = str;
				} else {
					this.valueElement.innerHTML = str;
				}
			}
		};


		this.setAlphaElementValue = function (str) {
			if (this.alphaElement) {
				if (jsc.nodeName(this.alphaElement) === 'input') {
					this.alphaElement.value = str;
				} else {
					this.alphaElement.innerHTML = str;
				}
			}
		};


		this._processParentElementsInDOM = function () {
			if (this._parentElementsProcessed) { return; }
			this._parentElementsProcessed = true;

			var elm = this.targetElement;
			do {
				// If the target element or one of its parent nodes has fixed position,
				// then use fixed positioning instead
				var compStyle = jsc.getCompStyle(elm);
				if (compStyle.position && compStyle.position.toLowerCase() === 'fixed') {
					this.fixed = true;
				}

				if (elm !== this.targetElement) {
					// Ensure to attach onParentScroll only once to each parent element
					// (multiple targetElements can share the same parent nodes)
					//
					// Note: It's not just offsetParents that can be scrollable,
					// that's why we loop through all parent nodes
					if (!jsc.getData(elm, 'hasScrollListener')) {
						elm.addEventListener('scroll', jsc.onParentScroll, false);
						jsc.setData(elm, 'hasScrollListener', true);
					}
				}
			} while ((elm = elm.parentNode) && jsc.nodeName(elm) !== 'body');
		};


		this.tryHide = function () {
			if (this.hideOnLeave) {
				this.hide();
			}
		};


		this.set__palette = function (val) {
			this.palette = val;
			this._palette = jsc.parsePaletteValue(val);
			this._paletteHasTransparency = jsc.containsTranparentColor(this._palette);
		};


		function setOption (option, value) {
			if (typeof option !== 'string') {
				throw new Error('Invalid value for option name: ' + option);
			}

			// enum option
			if (jsc.enumOpts.hasOwnProperty(option)) {
				if (typeof value === 'string') { // enum string values are case insensitive
					value = value.toLowerCase();
				}
				if (jsc.enumOpts[option].indexOf(value) === -1) {
					throw new Error('Option \'' + option + '\' has invalid value: ' + value);
				}
			}

			// deprecated option
			if (jsc.deprecatedOpts.hasOwnProperty(option)) {
				var oldOpt = option;
				var newOpt = jsc.deprecatedOpts[option];
				if (newOpt) {
					// if we have a new name for this option, let's log a warning and use the new name
					console.warn('Option \'%s\' is DEPRECATED, using \'%s\' instead.' + jsc.docsRef, oldOpt, newOpt);
					option = newOpt;
				} else {
					// new name not available for the option
					throw new Error('Option \'' + option + '\' is DEPRECATED');
				}
			}

			var setter = 'set__' + option;

			if (typeof THIS[setter] === 'function') { // a setter exists for this option
				THIS[setter](value);
				return true;

			} else if (option in THIS) { // option exists as a property
				THIS[option] = value;
				return true;
			}

			throw new Error('Unrecognized configuration option: ' + option);
		}


		function getOption (option) {
			if (typeof option !== 'string') {
				throw new Error('Invalid value for option name: ' + option);
			}

			// deprecated option
			if (jsc.deprecatedOpts.hasOwnProperty(option)) {
				var oldOpt = option;
				var newOpt = jsc.deprecatedOpts[option];
				if (newOpt) {
					// if we have a new name for this option, let's log a warning and use the new name
					console.warn('Option \'%s\' is DEPRECATED, using \'%s\' instead.' + jsc.docsRef, oldOpt, newOpt);
					option = newOpt;
				} else {
					// new name not available for the option
					throw new Error('Option \'' + option + '\' is DEPRECATED');
				}
			}

			var getter = 'get__' + option;

			if (typeof THIS[getter] === 'function') { // a getter exists for this option
				return THIS[getter](value);

			} else if (option in THIS) { // option exists as a property
				return THIS[option];
			}

			throw new Error('Unrecognized configuration option: ' + option);
		}


		function detachPicker () {
			jsc.removeClass(THIS.targetElement, jsc.pub.activeClassName);
			jsc.picker.wrap.parentNode.removeChild(jsc.picker.wrap);
			delete jsc.picker.owner;
		}


		function drawPicker () {

			// At this point, when drawing the picker, we know what the parent elements are
			// and we can do all related DOM operations, such as registering events on them
			// or checking their positioning
			THIS._processParentElementsInDOM();

			if (!jsc.picker) {
				jsc.picker = {
					owner: null, // owner picker instance
					wrap : jsc.createEl('div'),
					box : jsc.createEl('div'),
					boxS : jsc.createEl('div'), // shadow area
					boxB : jsc.createEl('div'), // border
					pad : jsc.createEl('div'),
					padB : jsc.createEl('div'), // border
					padM : jsc.createEl('div'), // mouse/touch area
					padCanvas : jsc.createPadCanvas(),
					cross : jsc.createEl('div'),
					crossBY : jsc.createEl('div'), // border Y
					crossBX : jsc.createEl('div'), // border X
					crossLY : jsc.createEl('div'), // line Y
					crossLX : jsc.createEl('div'), // line X
					sld : jsc.createEl('div'), // slider
					sldB : jsc.createEl('div'), // border
					sldM : jsc.createEl('div'), // mouse/touch area
					sldGrad : jsc.createSliderGradient(),
					sldPtrS : jsc.createEl('div'), // slider pointer spacer
					sldPtrIB : jsc.createEl('div'), // slider pointer inner border
					sldPtrMB : jsc.createEl('div'), // slider pointer middle border
					sldPtrOB : jsc.createEl('div'), // slider pointer outer border
					asld : jsc.createEl('div'), // alpha slider
					asldB : jsc.createEl('div'), // border
					asldM : jsc.createEl('div'), // mouse/touch area
					asldGrad : jsc.createASliderGradient(),
					asldPtrS : jsc.createEl('div'), // slider pointer spacer
					asldPtrIB : jsc.createEl('div'), // slider pointer inner border
					asldPtrMB : jsc.createEl('div'), // slider pointer middle border
					asldPtrOB : jsc.createEl('div'), // slider pointer outer border
					pal : jsc.createEl('div'), // palette
					btn : jsc.createEl('div'),
					btnT : jsc.createEl('div'), // text
				};

				jsc.picker.pad.appendChild(jsc.picker.padCanvas.elm);
				jsc.picker.padB.appendChild(jsc.picker.pad);
				jsc.picker.cross.appendChild(jsc.picker.crossBY);
				jsc.picker.cross.appendChild(jsc.picker.crossBX);
				jsc.picker.cross.appendChild(jsc.picker.crossLY);
				jsc.picker.cross.appendChild(jsc.picker.crossLX);
				jsc.picker.padB.appendChild(jsc.picker.cross);
				jsc.picker.box.appendChild(jsc.picker.padB);
				jsc.picker.box.appendChild(jsc.picker.padM);

				jsc.picker.sld.appendChild(jsc.picker.sldGrad.elm);
				jsc.picker.sldB.appendChild(jsc.picker.sld);
				jsc.picker.sldB.appendChild(jsc.picker.sldPtrOB);
				jsc.picker.sldPtrOB.appendChild(jsc.picker.sldPtrMB);
				jsc.picker.sldPtrMB.appendChild(jsc.picker.sldPtrIB);
				jsc.picker.sldPtrIB.appendChild(jsc.picker.sldPtrS);
				jsc.picker.box.appendChild(jsc.picker.sldB);
				jsc.picker.box.appendChild(jsc.picker.sldM);

				jsc.picker.asld.appendChild(jsc.picker.asldGrad.elm);
				jsc.picker.asldB.appendChild(jsc.picker.asld);
				jsc.picker.asldB.appendChild(jsc.picker.asldPtrOB);
				jsc.picker.asldPtrOB.appendChild(jsc.picker.asldPtrMB);
				jsc.picker.asldPtrMB.appendChild(jsc.picker.asldPtrIB);
				jsc.picker.asldPtrIB.appendChild(jsc.picker.asldPtrS);
				jsc.picker.box.appendChild(jsc.picker.asldB);
				jsc.picker.box.appendChild(jsc.picker.asldM);

				jsc.picker.box.appendChild(jsc.picker.pal);

				jsc.picker.btn.appendChild(jsc.picker.btnT);
				jsc.picker.box.appendChild(jsc.picker.btn);

				jsc.picker.boxB.appendChild(jsc.picker.box);
				jsc.picker.wrap.appendChild(jsc.picker.boxS);
				jsc.picker.wrap.appendChild(jsc.picker.boxB);

				jsc.picker.wrap.addEventListener('touchstart', jsc.onPickerTouchStart,
					jsc.isPassiveEventSupported ? {passive: false} : false);
			}

			var p = jsc.picker;

			var displaySlider = !!jsc.getSliderChannel(THIS);
			var displayAlphaSlider = THIS.hasAlphaChannel();
			var pickerDims = jsc.getPickerDims(THIS);
			var crossOuterSize = (2 * THIS.pointerBorderWidth + THIS.pointerThickness + 2 * THIS.crossSize);
			var controlPadding = jsc.getControlPadding(THIS);
			var borderRadius = Math.min(
				THIS.borderRadius,
				Math.round(THIS.padding * Math.PI)); // px
			var padCursor = 'crosshair';

			// wrap
			p.wrap.className = 'jscolor-wrap';
			p.wrap.style.width = pickerDims.borderW + 'px';
			p.wrap.style.height = pickerDims.borderH + 'px';
			p.wrap.style.zIndex = THIS.zIndex;

			// picker
			p.box.className = 'jscolor-picker';
			p.box.style.width = pickerDims.paddedW + 'px';
			p.box.style.height = pickerDims.paddedH + 'px';

			// picker shadow
			p.boxS.className = 'jscolor-shadow';
			jsc.setBorderRadius(p.boxS, borderRadius + 'px');

			// picker border
			p.boxB.className = 'jscolor-border';
			p.boxB.style.border = THIS.borderWidth + 'px solid';
			p.boxB.style.borderColor = THIS.borderColor;
			p.boxB.style.background = THIS.backgroundColor;
			jsc.setBorderRadius(p.boxB, borderRadius + 'px');

			// IE hack:
			// If the element is transparent, IE will trigger the event on the elements under it,
			// e.g. on Canvas or on elements with border
			p.padM.style.background = 'rgba(255,0,0,.2)';
			p.sldM.style.background = 'rgba(0,255,0,.2)';
			p.asldM.style.background = 'rgba(0,0,255,.2)';

			p.padM.style.opacity =
			p.sldM.style.opacity =
			p.asldM.style.opacity =
				'0';

			// pad
			p.pad.style.position = 'relative';
			p.pad.style.width = THIS.width + 'px';
			p.pad.style.height = THIS.height + 'px';

			// pad - color spectrum (HSV and HVS)
			p.padCanvas.draw(THIS.width, THIS.height, jsc.getPadYChannel(THIS));

			// pad border
			p.padB.style.position = 'absolute';
			p.padB.style.left = THIS.padding + 'px';
			p.padB.style.top = THIS.padding + 'px';
			p.padB.style.border = THIS.controlBorderWidth + 'px solid';
			p.padB.style.borderColor = THIS.controlBorderColor;

			// pad mouse area
			p.padM.style.position = 'absolute';
			p.padM.style.left = 0 + 'px';
			p.padM.style.top = 0 + 'px';
			p.padM.style.width = (THIS.padding + 2 * THIS.controlBorderWidth + THIS.width + controlPadding) + 'px';
			p.padM.style.height = (2 * THIS.controlBorderWidth + 2 * THIS.padding + THIS.height) + 'px';
			p.padM.style.cursor = padCursor;
			jsc.setData(p.padM, {
				instance: THIS,
				control: 'pad',
			})

			// pad cross
			p.cross.style.position = 'absolute';
			p.cross.style.left =
			p.cross.style.top =
				'0';
			p.cross.style.width =
			p.cross.style.height =
				crossOuterSize + 'px';

			// pad cross border Y and X
			p.crossBY.style.position =
			p.crossBX.style.position =
				'absolute';
			p.crossBY.style.background =
			p.crossBX.style.background =
				THIS.pointerBorderColor;
			p.crossBY.style.width =
			p.crossBX.style.height =
				(2 * THIS.pointerBorderWidth + THIS.pointerThickness) + 'px';
			p.crossBY.style.height =
			p.crossBX.style.width =
				crossOuterSize + 'px';
			p.crossBY.style.left =
			p.crossBX.style.top =
				(Math.floor(crossOuterSize / 2) - Math.floor(THIS.pointerThickness / 2) - THIS.pointerBorderWidth) + 'px';
			p.crossBY.style.top =
			p.crossBX.style.left =
				'0';

			// pad cross line Y and X
			p.crossLY.style.position =
			p.crossLX.style.position =
				'absolute';
			p.crossLY.style.background =
			p.crossLX.style.background =
				THIS.pointerColor;
			p.crossLY.style.height =
			p.crossLX.style.width =
				(crossOuterSize - 2 * THIS.pointerBorderWidth) + 'px';
			p.crossLY.style.width =
			p.crossLX.style.height =
				THIS.pointerThickness + 'px';
			p.crossLY.style.left =
			p.crossLX.style.top =
				(Math.floor(crossOuterSize / 2) - Math.floor(THIS.pointerThickness / 2)) + 'px';
			p.crossLY.style.top =
			p.crossLX.style.left =
				THIS.pointerBorderWidth + 'px';


			// slider
			p.sld.style.overflow = 'hidden';
			p.sld.style.width = THIS.sliderSize + 'px';
			p.sld.style.height = THIS.height + 'px';

			// slider gradient
			p.sldGrad.draw(THIS.sliderSize, THIS.height, '#000', '#000');

			// slider border
			p.sldB.style.display = displaySlider ? 'block' : 'none';
			p.sldB.style.position = 'absolute';
			p.sldB.style.left = (THIS.padding + THIS.width + 2 * THIS.controlBorderWidth + 2 * controlPadding) + 'px';
			p.sldB.style.top = THIS.padding + 'px';
			p.sldB.style.border = THIS.controlBorderWidth + 'px solid';
			p.sldB.style.borderColor = THIS.controlBorderColor;

			// slider mouse area
			p.sldM.style.display = displaySlider ? 'block' : 'none';
			p.sldM.style.position = 'absolute';
			p.sldM.style.left = (THIS.padding + THIS.width + 2 * THIS.controlBorderWidth + controlPadding) + 'px';
			p.sldM.style.top = 0 + 'px';
			p.sldM.style.width = (
					(THIS.sliderSize + 2 * controlPadding + 2 * THIS.controlBorderWidth) +
					(displayAlphaSlider ? 0 : Math.max(0, THIS.padding - controlPadding)) // remaining padding to the right edge
				) + 'px';
			p.sldM.style.height = (2 * THIS.controlBorderWidth + 2 * THIS.padding + THIS.height) + 'px';
			p.sldM.style.cursor = 'default';
			jsc.setData(p.sldM, {
				instance: THIS,
				control: 'sld',
			});

			// slider pointer inner and outer border
			p.sldPtrIB.style.border =
			p.sldPtrOB.style.border =
				THIS.pointerBorderWidth + 'px solid ' + THIS.pointerBorderColor;

			// slider pointer outer border
			p.sldPtrOB.style.position = 'absolute';
			p.sldPtrOB.style.left = -(2 * THIS.pointerBorderWidth + THIS.pointerThickness) + 'px';
			p.sldPtrOB.style.top = '0';

			// slider pointer middle border
			p.sldPtrMB.style.border = THIS.pointerThickness + 'px solid ' + THIS.pointerColor;

			// slider pointer spacer
			p.sldPtrS.style.width = THIS.sliderSize + 'px';
			p.sldPtrS.style.height = jsc.pub.sliderInnerSpace + 'px';


			// alpha slider
			p.asld.style.overflow = 'hidden';
			p.asld.style.width = THIS.sliderSize + 'px';
			p.asld.style.height = THIS.height + 'px';

			// alpha slider gradient
			p.asldGrad.draw(THIS.sliderSize, THIS.height, '#000');

			// alpha slider border
			p.asldB.style.display = displayAlphaSlider ? 'block' : 'none';
			p.asldB.style.position = 'absolute';
			p.asldB.style.left = (
					(THIS.padding + THIS.width + 2 * THIS.controlBorderWidth + controlPadding) +
					(displaySlider ? (THIS.sliderSize + 3 * controlPadding + 2 * THIS.controlBorderWidth) : 0)
				) + 'px';
			p.asldB.style.top = THIS.padding + 'px';
			p.asldB.style.border = THIS.controlBorderWidth + 'px solid';
			p.asldB.style.borderColor = THIS.controlBorderColor;

			// alpha slider mouse area
			p.asldM.style.display = displayAlphaSlider ? 'block' : 'none';
			p.asldM.style.position = 'absolute';
			p.asldM.style.left = (
					(THIS.padding + THIS.width + 2 * THIS.controlBorderWidth + controlPadding) +
					(displaySlider ? (THIS.sliderSize + 2 * controlPadding + 2 * THIS.controlBorderWidth) : 0)
				) + 'px';
			p.asldM.style.top = 0 + 'px';
			p.asldM.style.width = (
					(THIS.sliderSize + 2 * controlPadding + 2 * THIS.controlBorderWidth) +
					Math.max(0, THIS.padding - controlPadding) // remaining padding to the right edge
				) + 'px';
			p.asldM.style.height = (2 * THIS.controlBorderWidth + 2 * THIS.padding + THIS.height) + 'px';
			p.asldM.style.cursor = 'default';
			jsc.setData(p.asldM, {
				instance: THIS,
				control: 'asld',
			})

			// alpha slider pointer inner and outer border
			p.asldPtrIB.style.border =
			p.asldPtrOB.style.border =
				THIS.pointerBorderWidth + 'px solid ' + THIS.pointerBorderColor;

			// alpha slider pointer outer border
			p.asldPtrOB.style.position = 'absolute';
			p.asldPtrOB.style.left = -(2 * THIS.pointerBorderWidth + THIS.pointerThickness) + 'px';
			p.asldPtrOB.style.top = '0';

			// alpha slider pointer middle border
			p.asldPtrMB.style.border = THIS.pointerThickness + 'px solid ' + THIS.pointerColor;

			// alpha slider pointer spacer
			p.asldPtrS.style.width = THIS.sliderSize + 'px';
			p.asldPtrS.style.height = jsc.pub.sliderInnerSpace + 'px';


			// palette
			p.pal.className = 'jscolor-palette';
			p.pal.style.display = pickerDims.palette.rows ? 'block' : 'none';
			p.pal.style.left = THIS.padding + 'px';
			p.pal.style.top = (2 * THIS.controlBorderWidth + 2 * THIS.padding + THIS.height) + 'px';

			// palette's color samples

			p.pal.innerHTML = '';

			var chessboard = jsc.genColorPreviewCanvas('rgba(0,0,0,0)');

			var si = 0; // color sample's index
			for (var r = 0; r < pickerDims.palette.rows; r++) {
				for (var c = 0; c < pickerDims.palette.cols && si < THIS._palette.length; c++, si++) {
					var sampleColor = THIS._palette[si];
					var sampleCssColor = jsc.rgbaColor.apply(null, sampleColor.rgba);

					var sc = jsc.createEl('div'); // color sample's color
					sc.style.width = (pickerDims.palette.cellW - 2 * THIS.controlBorderWidth) + 'px';
					sc.style.height = (pickerDims.palette.cellH - 2 * THIS.controlBorderWidth) + 'px';
					sc.style.backgroundColor = sampleCssColor;

					var sw = jsc.createEl('div'); // color sample's wrap
					sw.className = 'jscolor-palette-sw';
					sw.style.left =
						(
							pickerDims.palette.cols <= 1 ? 0 :
							Math.round(10 * (c * ((pickerDims.contentW - pickerDims.palette.cellW) / (pickerDims.palette.cols - 1)))) / 10
						) + 'px';
					sw.style.top = (r * (pickerDims.palette.cellH + THIS.paletteSpacing)) + 'px';
					sw.style.border = THIS.controlBorderWidth + 'px solid';
					sw.style.borderColor = THIS.controlBorderColor;
					if (sampleColor.rgba[3] !== null && sampleColor.rgba[3] < 1.0) { // only create chessboard background if the sample has transparency
						sw.style.backgroundImage = 'url(\'' + chessboard.canvas.toDataURL() + '\')';
						sw.style.backgroundRepeat = 'repeat';
						sw.style.backgroundPosition = 'center center';
					}
					jsc.setData(sw, {
						instance: THIS,
						control: 'palette-sw',
						color: sampleColor,
					});
					sw.addEventListener('click', jsc.onPaletteSampleClick, false);
					sw.appendChild(sc);
					p.pal.appendChild(sw);
				}
			}


			// the Close button
			function setBtnBorder () {
				var insetColors = THIS.controlBorderColor.split(/\s+/);
				var outsetColor = insetColors.length < 2 ? insetColors[0] : insetColors[1] + ' ' + insetColors[0] + ' ' + insetColors[0] + ' ' + insetColors[1];
				p.btn.style.borderColor = outsetColor;
			}
			var btnPadding = 15; // px
			p.btn.className = 'jscolor-btn jscolor-btn-close';
			p.btn.style.display = THIS.closeButton ? 'block' : 'none';
			p.btn.style.left = THIS.padding + 'px';
			p.btn.style.bottom = THIS.padding + 'px';
			p.btn.style.padding = '0 ' + btnPadding + 'px';
			p.btn.style.maxWidth = (pickerDims.contentW - 2 * THIS.controlBorderWidth - 2 * btnPadding) + 'px';
			p.btn.style.height = THIS.buttonHeight + 'px';
			p.btn.style.border = THIS.controlBorderWidth + 'px solid';
			setBtnBorder();
			p.btn.style.color = THIS.buttonColor;
			p.btn.onmousedown = function () {
				THIS.hide();
			};
			p.btnT.style.display = 'inline';
			p.btnT.style.lineHeight = THIS.buttonHeight + 'px';
			p.btnT.innerText = THIS.closeText;

			// reposition the pointers
			redrawPad();
			redrawSld();
			redrawASld();

			// If we are changing the owner without first closing the picker,
			// make sure to first deal with the old owner
			if (jsc.picker.owner && jsc.picker.owner !== THIS) {
				jsc.removeClass(jsc.picker.owner.targetElement, jsc.pub.activeClassName);
			}

			// Set a new picker owner
			jsc.picker.owner = THIS;

			// The redrawPosition() method needs picker.owner to be set, that's why we call it here,
			// after setting the owner
			jsc.redrawPosition();

			if (p.wrap.parentNode !== THIS.container) {
				THIS.container.appendChild(p.wrap);
			}

			jsc.addClass(THIS.targetElement, jsc.pub.activeClassName);
		}


		function redrawPad () {
			// redraw the pad pointer
			var yChannel = jsc.getPadYChannel(THIS);
			var x = Math.round((THIS.channels.h / 360) * (THIS.width - 1));
			var y = Math.round((1 - THIS.channels[yChannel] / 100) * (THIS.height - 1));
			var crossOuterSize = (2 * THIS.pointerBorderWidth + THIS.pointerThickness + 2 * THIS.crossSize);
			var ofs = -Math.floor(crossOuterSize / 2);
			jsc.picker.cross.style.left = (x + ofs) + 'px';
			jsc.picker.cross.style.top = (y + ofs) + 'px';

			// redraw the slider
			switch (jsc.getSliderChannel(THIS)) {
			case 's':
				var rgb1 = jsc.HSV_RGB(THIS.channels.h, 100, THIS.channels.v);
				var rgb2 = jsc.HSV_RGB(THIS.channels.h, 0, THIS.channels.v);
				var color1 = 'rgb(' +
					Math.round(rgb1[0]) + ',' +
					Math.round(rgb1[1]) + ',' +
					Math.round(rgb1[2]) + ')';
				var color2 = 'rgb(' +
					Math.round(rgb2[0]) + ',' +
					Math.round(rgb2[1]) + ',' +
					Math.round(rgb2[2]) + ')';
				jsc.picker.sldGrad.draw(THIS.sliderSize, THIS.height, color1, color2);
				break;
			case 'v':
				var rgb = jsc.HSV_RGB(THIS.channels.h, THIS.channels.s, 100);
				var color1 = 'rgb(' +
					Math.round(rgb[0]) + ',' +
					Math.round(rgb[1]) + ',' +
					Math.round(rgb[2]) + ')';
				var color2 = '#000';
				jsc.picker.sldGrad.draw(THIS.sliderSize, THIS.height, color1, color2);
				break;
			}

			// redraw the alpha slider
			jsc.picker.asldGrad.draw(THIS.sliderSize, THIS.height, THIS.toHEXString());
		}


		function redrawSld () {
			var sldChannel = jsc.getSliderChannel(THIS);
			if (sldChannel) {
				// redraw the slider pointer
				var y = Math.round((1 - THIS.channels[sldChannel] / 100) * (THIS.height - 1));
				jsc.picker.sldPtrOB.style.top = (y - (2 * THIS.pointerBorderWidth + THIS.pointerThickness) - Math.floor(jsc.pub.sliderInnerSpace / 2)) + 'px';
			}

			// redraw the alpha slider
			jsc.picker.asldGrad.draw(THIS.sliderSize, THIS.height, THIS.toHEXString());
		}


		function redrawASld () {
			var y = Math.round((1 - THIS.channels.a) * (THIS.height - 1));
			jsc.picker.asldPtrOB.style.top = (y - (2 * THIS.pointerBorderWidth + THIS.pointerThickness) - Math.floor(jsc.pub.sliderInnerSpace / 2)) + 'px';
		}


		function isPickerOwner () {
			return jsc.picker && jsc.picker.owner === THIS;
		}


		function onValueKeyDown (ev) {
			if (jsc.eventKey(ev) === 'Enter') {
				if (THIS.valueElement) {
					THIS.processValueInput(THIS.valueElement.value);
				}
				THIS.tryHide();
			}
		}


		function onAlphaKeyDown (ev) {
			if (jsc.eventKey(ev) === 'Enter') {
				if (THIS.alphaElement) {
					THIS.processAlphaInput(THIS.alphaElement.value);
				}
				THIS.tryHide();
			}
		}


		function onValueChange (ev) {
			if (jsc.getData(ev, 'internal')) {
				return; // skip if the event was internally triggered by jscolor
			}

			var oldVal = THIS.valueElement.value;

			THIS.processValueInput(THIS.valueElement.value); // this might change the value

			jsc.triggerCallback(THIS, 'onChange');

			if (THIS.valueElement.value !== oldVal) {
				// value was additionally changed -> let's trigger the change event again, even though it was natively dispatched
				jsc.triggerInputEvent(THIS.valueElement, 'change', true, true);
			}
		}


		function onAlphaChange (ev) {
			if (jsc.getData(ev, 'internal')) {
				return; // skip if the event was internally triggered by jscolor
			}

			var oldVal = THIS.alphaElement.value;

			THIS.processAlphaInput(THIS.alphaElement.value); // this might change the value

			jsc.triggerCallback(THIS, 'onChange');

			// triggering valueElement's onChange (because changing alpha changes the entire color, e.g. with rgba format)
			jsc.triggerInputEvent(THIS.valueElement, 'change', true, true);

			if (THIS.alphaElement.value !== oldVal) {
				// value was additionally changed -> let's trigger the change event again, even though it was natively dispatched
				jsc.triggerInputEvent(THIS.alphaElement, 'change', true, true);
			}
		}


		function onValueInput (ev) {
			if (jsc.getData(ev, 'internal')) {
				return; // skip if the event was internally triggered by jscolor
			}

			if (THIS.valueElement) {
				THIS.fromString(THIS.valueElement.value, jsc.flags.leaveValue);
			}

			jsc.triggerCallback(THIS, 'onInput');

			// triggering valueElement's onInput
			// (not needed, it was dispatched normally by the browser)
		}


		function onAlphaInput (ev) {
			if (jsc.getData(ev, 'internal')) {
				return; // skip if the event was internally triggered by jscolor
			}

			if (THIS.alphaElement) {
				THIS.fromHSVA(null, null, null, parseFloat(THIS.alphaElement.value), jsc.flags.leaveAlpha);
			}

			jsc.triggerCallback(THIS, 'onInput');

			// triggering valueElement's onInput (because changing alpha changes the entire color, e.g. with rgba format)
			jsc.triggerInputEvent(THIS.valueElement, 'input', true, true);
		}


		// let's process the DEPRECATED 'options' property (this will be later removed)
		if (jsc.pub.options) {
			// let's set custom default options, if specified
			for (var opt in jsc.pub.options) {
				if (jsc.pub.options.hasOwnProperty(opt)) {
					try {
						setOption(opt, jsc.pub.options[opt]);
					} catch (e) {
						console.warn(e);
					}
				}
			}
		}


		// let's apply configuration presets
		//
		var presetsArr = [];

		if (opts.preset) {
			if (typeof opts.preset === 'string') {
				presetsArr = opts.preset.split(/\s+/);
			} else if (Array.isArray(opts.preset)) {
				presetsArr = opts.preset.slice(); // slice() to clone
			} else {
				console.warn('Unrecognized preset value');
			}
		}

		// always use the 'default' preset. If it's not listed, append it to the end.
		if (presetsArr.indexOf('default') === -1) {
			presetsArr.push('default');
		}

		// let's apply the presets in reverse order, so that should there be any overlapping options,
		// the formerly listed preset will override the latter
		for (var i = presetsArr.length - 1; i >= 0; i -= 1) {
			var pres = presetsArr[i];
			if (!pres) {
				continue; // preset is empty string
			}
			if (!jsc.pub.presets.hasOwnProperty(pres)) {
				console.warn('Unknown preset: %s', pres);
				continue;
			}
			for (var opt in jsc.pub.presets[pres]) {
				if (jsc.pub.presets[pres].hasOwnProperty(opt)) {
					try {
						setOption(opt, jsc.pub.presets[pres][opt]);
					} catch (e) {
						console.warn(e);
					}
				}
			}
		}


		// let's set specific options for this color picker
		var nonProperties = [
			// these options won't be set as instance properties
			'preset',
		];
		for (var opt in opts) {
			if (opts.hasOwnProperty(opt)) {
				if (nonProperties.indexOf(opt) === -1) {
					try {
						setOption(opt, opts[opt]);
					} catch (e) {
						console.warn(e);
					}
				}
			}
		}


		//
		// Install the color picker on chosen element(s)
		//


		// Determine picker's container element
		if (this.container === undefined) {
			this.container = window.document.body; // default container is BODY element

		} else { // explicitly set to custom element
			this.container = jsc.node(this.container);
		}

		if (!this.container) {
			throw new Error('Cannot instantiate color picker without a container element');
		}


		// Fetch the target element
		this.targetElement = jsc.node(targetElement);

		if (!this.targetElement) {
			// temporarily customized error message to help with migrating from versions prior to 2.2
			if (typeof targetElement === 'string' && /^[a-zA-Z][\w:.-]*$/.test(targetElement)) {
				// targetElement looks like valid ID
				var possiblyId = targetElement;
				throw new Error('If \'' + possiblyId + '\' is supposed to be an ID, please use \'#' + possiblyId + '\' or any valid CSS selector.');
			}

			throw new Error('Cannot instantiate color picker without a target element');
		}

		if (this.targetElement.jscolor && this.targetElement.jscolor instanceof jsc.pub) {
			throw new Error('Color picker already installed on this element');
		}


		// link this instance with the target element
		this.targetElement.jscolor = this;
		jsc.addClass(this.targetElement, jsc.pub.className);

		// register this instance
		jsc.instances.push(this);


		// if target is BUTTON
		if (jsc.isButton(this.targetElement)) {

			if (this.targetElement.type.toLowerCase() !== 'button') {
				// on buttons, always force type to be 'button', e.g. in situations the target <button> has no type
				// and thus defaults to 'submit' and would submit the form when clicked
				this.targetElement.type = 'button';
			}

			if (jsc.isButtonEmpty(this.targetElement)) { // empty button
				// it is important to clear element's contents first.
				// if we're re-instantiating color pickers on DOM that has been modified by changing page's innerHTML,
				// we would keep adding more non-breaking spaces to element's content (because element's contents survive
				// innerHTML changes, but picker instances don't)
				jsc.removeChildren(this.targetElement);

				// let's insert a non-breaking space
				this.targetElement.appendChild(window.document.createTextNode('\xa0'));

				// set min-width = previewSize, if not already greater
				var compStyle = jsc.getCompStyle(this.targetElement);
				var currMinWidth = parseFloat(compStyle['min-width']) || 0;
				if (currMinWidth < this.previewSize) {
					jsc.setStyle(this.targetElement, {
						'min-width': this.previewSize + 'px',
					}, this.forceStyle);
				}
			}
		}

		// Determine the value element
		if (this.valueElement === undefined) {
			if (jsc.isTextInput(this.targetElement)) {
				// for text inputs, default valueElement is targetElement
				this.valueElement = this.targetElement;
			} else {
				// leave it undefined
			}

		} else if (this.valueElement === null) { // explicitly set to null
			// leave it null

		} else { // explicitly set to custom element
			this.valueElement = jsc.node(this.valueElement);
		}

		// Determine the alpha element
		if (this.alphaElement) {
			this.alphaElement = jsc.node(this.alphaElement);
		}

		// Determine the preview element
		if (this.previewElement === undefined) {
			this.previewElement = this.targetElement; // default previewElement is targetElement

		} else if (this.previewElement === null) { // explicitly set to null
			// leave it null

		} else { // explicitly set to custom element
			this.previewElement = jsc.node(this.previewElement);
		}

		// valueElement
		if (this.valueElement && jsc.isTextInput(this.valueElement)) {

			// If the value element has onInput event already set, we need to detach it and attach AFTER our listener.
			// otherwise the picker instance would still contain the old color when accessed from the onInput handler.
			var valueElementOrigEvents = {
				onInput: this.valueElement.oninput
			};
			this.valueElement.oninput = null;

			this.valueElement.addEventListener('keydown', onValueKeyDown, false);
			this.valueElement.addEventListener('change', onValueChange, false);
			this.valueElement.addEventListener('input', onValueInput, false);
			// the original event listener must be attached AFTER our handler (to let it first set picker's color)
			if (valueElementOrigEvents.onInput) {
				this.valueElement.addEventListener('input', valueElementOrigEvents.onInput, false);
			}

			this.valueElement.setAttribute('autocomplete', 'off');
			this.valueElement.setAttribute('autocorrect', 'off');
			this.valueElement.setAttribute('autocapitalize', 'off');
			this.valueElement.setAttribute('spellcheck', false);
		}

		// alphaElement
		if (this.alphaElement && jsc.isTextInput(this.alphaElement)) {
			this.alphaElement.addEventListener('keydown', onAlphaKeyDown, false);
			this.alphaElement.addEventListener('change', onAlphaChange, false);
			this.alphaElement.addEventListener('input', onAlphaInput, false);

			this.alphaElement.setAttribute('autocomplete', 'off');
			this.alphaElement.setAttribute('autocorrect', 'off');
			this.alphaElement.setAttribute('autocapitalize', 'off');
			this.alphaElement.setAttribute('spellcheck', false);
		}

		// determine initial color value
		//
		var initValue = 'FFFFFF';

		if (this.value !== undefined) {
			initValue = this.value; // get initial color from the 'value' property
		} else if (this.valueElement && this.valueElement.value !== undefined) {
			initValue = this.valueElement.value; // get initial color from valueElement's value
		}

		// determine initial alpha value
		//
		var initAlpha = undefined;

		if (this.alpha !== undefined) {
			initAlpha = (''+this.alpha); // get initial alpha value from the 'alpha' property
		} else if (this.alphaElement && this.alphaElement.value !== undefined) {
			initAlpha = this.alphaElement.value; // get initial color from alphaElement's value
		}

		// determine current format based on the initial color value
		//
		this._currentFormat = null;

		if (['auto', 'any'].indexOf(this.format.toLowerCase()) > -1) {
			// format is 'auto' or 'any' -> let's auto-detect current format
			var color = jsc.parseColorString(initValue);
			this._currentFormat = color ? color.format : 'hex';
		} else {
			// format is specified
			this._currentFormat = this.format.toLowerCase();
		}


		// let's parse the initial color value and expose color's preview
		this.processValueInput(initValue);

		// let's also parse and expose the initial alpha value, if any
		//
		// Note: If the initial color value contains alpha value in it (e.g. in rgba format),
		// this will overwrite it. So we should only process alpha input if there was initial
		// alpha explicitly set, otherwise we could needlessly lose initial value's alpha
		if (initAlpha !== undefined) {
			this.processAlphaInput(initAlpha);
		}

		if (this.random) {
			// randomize the initial color value
			this.randomize.apply(this, Array.isArray(this.random) ? this.random : []);
		}

	}

};


//================================
// Public properties and methods
//================================

//
// These will be publicly available via jscolor.<name> and JSColor.<name>
//


// class that will be set to elements having jscolor installed on them
jsc.pub.className = 'jscolor';


// class that will be set to elements having jscolor active on them
jsc.pub.activeClassName = 'jscolor-active';


// whether to try to parse the options string by evaluating it using 'new Function()'
// in case it could not be parsed with JSON.parse()
jsc.pub.looseJSON = true;


// presets
jsc.pub.presets = {};

// built-in presets
jsc.pub.presets['default'] = {}; // baseline for customization

jsc.pub.presets['light'] = { // default color scheme
	backgroundColor: 'rgba(255,255,255,1)',
	controlBorderColor: 'rgba(187,187,187,1)',
	buttonColor: 'rgba(0,0,0,1)',
};
jsc.pub.presets['dark'] = {
	backgroundColor: 'rgba(51,51,51,1)',
	controlBorderColor: 'rgba(153,153,153,1)',
	buttonColor: 'rgba(240,240,240,1)',
};

jsc.pub.presets['small'] = { width:101, height:101, padding:10, sliderSize:14, paletteCols:8 };
jsc.pub.presets['medium'] = { width:181, height:101, padding:12, sliderSize:16, paletteCols:10 }; // default size
jsc.pub.presets['large'] = { width:271, height:151, padding:12, sliderSize:24, paletteCols:15 };

jsc.pub.presets['thin'] = { borderWidth:1, controlBorderWidth:1, pointerBorderWidth:1 }; // default thickness
jsc.pub.presets['thick'] = { borderWidth:2, controlBorderWidth:2, pointerBorderWidth:2 };


// size of space in the sliders
jsc.pub.sliderInnerSpace = 3; // px

// transparency chessboard
jsc.pub.chessboardSize = 8; // px
jsc.pub.chessboardColor1 = '#666666';
jsc.pub.chessboardColor2 = '#999999';

// preview separator
jsc.pub.previewSeparator = ['rgba(255,255,255,.65)', 'rgba(128,128,128,.65)'];


// Initializes jscolor
jsc.pub.init = function () {
	if (jsc.initialized) {
		return;
	}

	// attach some necessary handlers
	window.document.addEventListener('mousedown', jsc.onDocumentMouseDown, false);
	window.document.addEventListener('keyup', jsc.onDocumentKeyUp, false);
	window.addEventListener('resize', jsc.onWindowResize, false);
	window.addEventListener('scroll', jsc.onWindowScroll, false);

	// append default CSS to HEAD
	jsc.appendDefaultCss();

	// install jscolor on current DOM
	jsc.pub.install();

	jsc.initialized = true;

	// call functions waiting in the queue
	while (jsc.readyQueue.length) {
		var func = jsc.readyQueue.shift();
		func();
	}
};


// Installs jscolor on current DOM tree
jsc.pub.install = function (rootNode) {
	var success = true;

	try {
		jsc.installBySelector('[data-jscolor]', rootNode);
	} catch (e) {
		success = false;
		console.warn(e);
	}

	// for backward compatibility with DEPRECATED installation using class name
	if (jsc.pub.lookupClass) {
		try {
			jsc.installBySelector(
				(
					'input.' + jsc.pub.lookupClass + ', ' +
					'button.' + jsc.pub.lookupClass
				),
				rootNode
			);
		} catch (e) {}
	}

	return success;
};


// Registers function to be called as soon as jscolor is initialized (or immediately, if it already is).
//
jsc.pub.ready = function (func) {
	if (typeof func !== 'function') {
		console.warn('Passed value is not a function');
		return false;
	}

	if (jsc.initialized) {
		func();
	} else {
		jsc.readyQueue.push(func);
	}
	return true;
};


// Triggers given input event(s) (e.g. 'input' or 'change') on all color pickers.
//
// It is possible to specify multiple events separated with a space.
// If called before jscolor is initialized, then the events will be triggered after initialization.
//
jsc.pub.trigger = function (eventNames) {
	var triggerNow = function () {
		jsc.triggerGlobal(eventNames);
	};

	if (jsc.initialized) {
		triggerNow();
	} else {
		jsc.pub.ready(triggerNow);
	}
};


// Hides current color picker box
jsc.pub.hide = function () {
	if (jsc.picker && jsc.picker.owner) {
		jsc.picker.owner.hide();
	}
};


// Returns a data URL of a gray chessboard image that indicates transparency
jsc.pub.chessboard = function (color) {
	if (!color) {
		color = 'rgba(0,0,0,0)';
	}
	var preview = jsc.genColorPreviewCanvas(color);
	return preview.canvas.toDataURL();
};


// Returns a data URL of a gray chessboard image that indicates transparency
jsc.pub.background = function (color) {
	var backgrounds = [];

	// CSS gradient for background color preview
	backgrounds.push(jsc.genColorPreviewGradient(color));

	// data URL of generated PNG image with a gray transparency chessboard
	var preview = jsc.genColorPreviewCanvas();
	backgrounds.push([
		'url(\'' + preview.canvas.toDataURL() + '\')',
		'left top',
		'repeat',
	].join(' '));

	return backgrounds.join(', ');
};


//
// DEPRECATED properties and methods
//


// DEPRECATED. Use jscolor.presets.default instead.
//
// Custom default options for all color pickers, e.g. { hash: true, width: 300 }
jsc.pub.options = {};


// DEPRECATED. Use data-jscolor attribute instead, which installs jscolor on given element.
//
// By default, we'll search for all elements with class="jscolor" and install a color picker on them.
//
// You can change what class name will be looked for by setting the property jscolor.lookupClass
// anywhere in your HTML document. To completely disable the automatic lookup, set it to null.
//
jsc.pub.lookupClass = 'jscolor';


// DEPRECATED. Use data-jscolor attribute instead, which installs jscolor on given element.
//
// Install jscolor on all elements that have the specified class name
jsc.pub.installByClassName = function () {
	console.error('jscolor.installByClassName() is DEPRECATED. Use data-jscolor="" attribute instead of a class name.' + jsc.docsRef);
	return false;
};


jsc.register();


return jsc.pub;


})(); // END jscolor


if (typeof window.jscolor === 'undefined') {
	window.jscolor = window.JSColor = jscolor;
}


// END jscolor code

return jscolor;

}); // END factory


/***/ })

/******/ 	});
/************************************************************************/
/******/ 	// The module cache
/******/ 	var __webpack_module_cache__ = {};
/******/ 	
/******/ 	// The require function
/******/ 	function __webpack_require__(moduleId) {
/******/ 		// Check if module is in cache
/******/ 		var cachedModule = __webpack_module_cache__[moduleId];
/******/ 		if (cachedModule !== undefined) {
/******/ 			return cachedModule.exports;
/******/ 		}
/******/ 		// Create a new module (and put it into the cache)
/******/ 		var module = __webpack_module_cache__[moduleId] = {
/******/ 			// no module.id needed
/******/ 			// no module.loaded needed
/******/ 			exports: {}
/******/ 		};
/******/ 	
/******/ 		// Execute the module function
/******/ 		__webpack_modules__[moduleId].call(module.exports, module, module.exports, __webpack_require__);
/******/ 	
/******/ 		// Return the exports of the module
/******/ 		return module.exports;
/******/ 	}
/******/ 	
/************************************************************************/
/******/ 	/* webpack/runtime/compat get default export */
/******/ 	(() => {
/******/ 		// getDefaultExport function for compatibility with non-harmony modules
/******/ 		__webpack_require__.n = (module) => {
/******/ 			var getter = module && module.__esModule ?
/******/ 				() => (module['default']) :
/******/ 				() => (module);
/******/ 			__webpack_require__.d(getter, { a: getter });
/******/ 			return getter;
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/define property getters */
/******/ 	(() => {
/******/ 		// define getter functions for harmony exports
/******/ 		__webpack_require__.d = (exports, definition) => {
/******/ 			for(var key in definition) {
/******/ 				if(__webpack_require__.o(definition, key) && !__webpack_require__.o(exports, key)) {
/******/ 					Object.defineProperty(exports, key, { enumerable: true, get: definition[key] });
/******/ 				}
/******/ 			}
/******/ 		};
/******/ 	})();
/******/ 	
/******/ 	/* webpack/runtime/hasOwnProperty shorthand */
/******/ 	(() => {
/******/ 		__webpack_require__.o = (obj, prop) => (Object.prototype.hasOwnProperty.call(obj, prop))
/******/ 	})();
/******/ 	
/************************************************************************/
// This entry needs to be wrapped in an IIFE because it needs to be in strict mode.
(() => {
"use strict";

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/settingClasses/baseSetting.js
/** The basic setting class */
class Setting {
  constructor(defaultValue, type, group) {
    this.defaultValue = defaultValue;
    this.type = type;
    this.group = group;
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/settingClasses/settingColours.js


/** The colour picker setting class */
class SettingColours extends Setting {
  constructor(defaultValue, type, group, desc) {
    super(defaultValue, type, group);
    this.desc = desc;
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/settingClasses/settingInputNumber.js


/** The number input setting class */
class SettingInputNumber extends Setting {
  constructor(defaultValue, type, group, label, desc, min, max) {
    super(defaultValue, type, group);
    this.label = label;
    this.desc = desc;
    this.min = min;
    this.max = max;
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/settingClasses/settingKeycode.js


/** The setting class for keycodes */
class SettingKeycode extends Setting {
  constructor(defaultValue, type, group, desc) {
    super(defaultValue, type, group);
    this.desc = desc;
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/settingClasses/settingStandard.js


/** The standard toggle setting class */
class SettingStandard extends Setting {
  constructor(defaultValue, type, group, label, desc, toggle) {
    super(defaultValue, type, group);
    this.label = label;
    this.desc = desc;
    this.toggle = toggle;
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/settingClasses/settingStandardWithFunc.js


/** The standard toggle setting class with functions */
class SettingStandardWithFunc extends Setting {
  constructor(defaultValue, type, group, label, desc, toggle, func) {
    super(defaultValue, type, group);
    this.label = label;
    this.desc = desc;
    this.toggle = toggle;
    if (func !== undefined) {
      this.func = func;
    }
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/settingClasses/settingVolume.js


/** The volume level setting class */
class SettingVolume extends Setting {
  constructor(defaultValue, type, group, label, desc) {
    super(defaultValue, type, group);
    this.label = label;
    this.desc = desc;
    for (let i = 0; i < 101; i++) {
      this.label[i] = `${i}%`;
    }
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/notifications/prompt.js
/** Creates a Prompt similar to the base game fixing some of the stuff breaking them
 * @param 	{string}	content	  The outerHTML of the inputPrompt
 * @param 	{Array}		options	  An array containing labels and functions for the buttons of the prompt
 */
function cookieMonsterPrompt(content, options) {
  Game.promptWrapL.className = 'framed';
  Game.promptL.innerHTML = `${content}<div class="optionBox"></div>`;
  Object.keys(options).forEach((i) => {
    const option = document.createElement('a');
    option.id = `promptOption${i}`;
    option.className = 'option';
    option.onclick = function () {
      PlaySound('snd/tick.mp3');
      options[i][1]();
    };
    option.textContent = options[i][0]; // eslint-disable-line prefer-destructuring
    Game.promptL.children[1].appendChild(option);
  });
  Game.promptAnchorL.style.display = 'block';
  Game.darkenL.style.display = 'block';
  Game.promptL.focus();
  Game.promptOn = 1;
  Game.UpdatePrompt();
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/notifications/flash.js
/**
 * This function creates a flash depending on config
 * @param	{string}	modName	    The name of the mod
 * @param	{number}	mode	      Sets the intensity of the flash, used to recursively dim flash
 * 								              All initial calls of function have use mode === 3
 * @param	{string}	configName	The setting that is checked before creating the flash
 * @param	{bool}    forced	    Whether the sound should play regardless of settings, used to test the sound
 */

function createFlash(modName, mode, configName, forced) {
  // The arguments check makes the sound not play upon initialization of the mod
  if (
    ((Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] === 1 || forced) &&
      mode === 3 &&
      window.cookieMonsterFrameworkData.isInitializing === false) ||
    mode === 1
  ) {
    l('CMFlashScreen').style.backgroundColor =
      Game.mods.cookieMonsterFramework.saveData[modName].settings[`Colour${configName}`];
    l('CMFlashScreen').style.opacity = '0.5';
    if (mode === 3) {
      l('CMFlashScreen').style.display = 'inline';
      setTimeout(() => {
        createFlash(modName, 2, configName, true);
      }, 1000 / Game.fps);
    } else {
      setTimeout(() => {
        createFlash(modName, 0, configName, true);
      }, 1000 / Game.fps);
    }
  } else if (mode === 2) {
    l('CMFlashScreen').style.opacity = '1';
    setTimeout(() => {
      createFlash(modName, 1, configName, true);
    }, 1000 / Game.fps);
  } else if (mode === 0) l('CMFlashScreen').style.display = 'none';
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/menu/listings/createInfoListing.js
/**
 * Returns a subsection for the mod to add listings/info to
 * @param   {string}  listingHTML   The innerHTML of the listing
 * @returns {object}  listingDiv    Div of the subseciont
 */
function createInfoListing(listingHTML) {
  const listingDiv = document.createElement('div');
  listingDiv.className = 'listing';
  listingDiv.innerHTML = listingHTML;
  return listingDiv;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/savingAndLoading/saveFramework.js
/**
 * This function saves the settings and headers within the Framework without saving any of the other save-data
 * This allows saving in between the autosave intervals
 */
function saveFramework() {
  Object.keys(Game.mods.cookieMonsterFramework.saveData).forEach((modName) => {
    const modSaveString = JSON.stringify(Game.mods.cookieMonsterFramework.saveData[modName]);

    const cookieClickerSaveString = b64_to_utf8(
      unescape(localStorage.getItem('CookieClickerGame')).split('!END!')[0],
    );
    const pattern = new RegExp(`${modName}.*?(;|$)`);
    const modSave = cookieClickerSaveString.match(pattern);
    if (modSave !== null) {
      const newSaveString = cookieClickerSaveString.replace(
        modSave[0],
        `${modName}:${modSaveString}`,
      );
      localStorage.setItem('CookieClickerGame', escape(`${utf8_to_b64(newSaveString)}!END!`));
    }
  });
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/menu/toggles/toggleHeader.js


/**
 * This function toggles header options by incrementing them with 1 and handling changes
 * It is called by the onclick event of the +/- next to headers
 * @param 	{string}	config	The name of the header
 */
function toggleHeader(modName, headerName) {
  if (
    typeof Game.mods.cookieMonsterFramework.saveData[modName].headers[headerName] === 'undefined'
  ) {
    Game.mods.cookieMonsterFramework.saveData[modName].headers[headerName] = 1;
  }
  switch (Game.mods.cookieMonsterFramework.saveData[modName].headers[headerName]) {
    case 0:
      Game.mods.cookieMonsterFramework.saveData[modName].headers[headerName] = 1;
      break;
    default:
      Game.mods.cookieMonsterFramework.saveData[modName].headers[headerName] = 0;
      break;
  }
  saveFramework();
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/menu/createModMenuSection.js


/**
 * Returns a subsection for the mod to add listings/info to
 * @param   {string}  modName         The name of the mod (i.e., CookieMonster)
 * @param   {string}  modDisplayName  Display name of the mod (i.e., Cookie Monster)
 * @param   {string}  menuName        Name of the menu (i.e., Info, Options)
 * @returns {object}  modSectionDiv   Div of the subseciont
 */
function createModMenuSection(modName, modDisplayName, menuName) {
  const modSectionDiv = document.createElement('div');
  modSectionDiv.className = 'subsection';
  modSectionDiv.id = `${modName}MenuSection`;

  const titleDiv = document.createElement('div');
  titleDiv.className = 'title';
  titleDiv.style.fontSize = '18px';
  titleDiv.innerHTML = modDisplayName;

  const buttonSpan = document.createElement('span'); // Creates the +/- button
  buttonSpan.style.cursor = 'pointer';
  buttonSpan.style.display = 'inline-block';
  buttonSpan.style.height = '14px';
  buttonSpan.style.width = '14px';
  buttonSpan.style.borderRadius = '7px';
  buttonSpan.style.textAlign = 'center';
  buttonSpan.style.backgroundColor = '#C0C0C0';
  buttonSpan.style.color = 'black';
  buttonSpan.style.fontSize = '13px';
  buttonSpan.style.verticalAlign = 'middle';
  buttonSpan.textContent = Game.mods.cookieMonsterFramework.saveData[modName].headers[menuName]
    ? '-'
    : '+';
  buttonSpan.onclick = function () {
    toggleHeader(modName, menuName);
    Game.UpdateMenu();
  };

  titleDiv.appendChild(buttonSpan);

  modSectionDiv.appendChild(titleDiv);

  return modSectionDiv;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/notifications/notification.js
/**
 * This function creates a notifcation depending on config
 * @param	{string}	modName	    The name of the mod
 * @param	{string}	configName	The setting in CM.Options that is checked before creating the notification
 * @param	{string}	title			  The title of the to-be created notifications
 * @param	{string}	message			The text of the to-be created notifications
 */
function createNotification(modName, configName, title, message) {
  if (
    Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] === 1 &&
    document.visibilityState === 'hidden' &&
    window.cookieMonsterFrameworkData.isInitializing === false
  ) {
    // eslint-disable-next-line no-new
    new Notification(title, {
      body: message,
      badge: 'https://orteil.dashnet.org/cookieclicker/favicon.ico',
    });
  }
}

// EXTERNAL MODULE: ./node_modules/@eastdesire/jscolor/jscolor.js
var jscolor = __webpack_require__(75);
var jscolor_default = /*#__PURE__*/__webpack_require__.n(jscolor);
;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/menu/toggles/toggleFavourite.js


/**
 * This function toggles favourite settings by adding them to an array in the savedata
 * It is called by the onclick event of the favourite stars
 * @param 	{string}    modName	    The name of the mod
 * @param 	{string}	configName	The name of the setting
 */
function toggleFavouriteSetting(modName, configName) {
  if (Game.mods.cookieMonsterFramework.saveData[modName].favouriteSettings.includes(configName))
    Game.mods.cookieMonsterFramework.saveData[modName].favouriteSettings =
      Game.mods.cookieMonsterFramework.saveData[modName].favouriteSettings.filter(
        (ele) => ele !== configName,
      );
  else Game.mods.cookieMonsterFramework.saveData[modName].favouriteSettings.push(configName);
  saveFramework();
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/menu/listings/createOptionsFavouriteStar.js


/**
 * This function creates the favourite setting star div-object
 * @param 	{string} modName	  The name of the Mod
 * @param 	{string} configName	The name of the option
 * @parm    {array}  favourites An array with the names of all settings that are currently favourited
 * @returns	{object} div		    The option object
 */
function createFavouriteStar(modName, configName, favourites) {
  const FavStar = document.createElement('a');
  if (favourites.includes(configName)) {
    FavStar.innerText = '★';
    FavStar.style.color = 'yellow';
  } else FavStar.innerText = '☆';
  FavStar.className = 'option';
  FavStar.onclick = function () {
    toggleFavouriteSetting(modName, configName);
    saveFramework();
    Game.UpdateMenu();
  };
  FavStar.onmouseover = function () {
    Game.tooltip.draw(
      this,
      escape(
        '<div style="min-width: 250px; margin-bottom: 4px;"><div style="text-align: left;">Click to set this setting as favourite and show it in \'favourite\' settings at the top of the Cookie Monster Settings</div></div>',
      ),
    );
  };
  FavStar.onmouseout = function () {
    Game.tooltip.hide();
  };
  FavStar.appendChild(document.createTextNode(' '));
  return FavStar;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/notifications/sound.js
/**
 * This function plays a sound depending on config
 * @param	{string}	modName	    The name of the mod
 * @param	{variable}	url			A variable that gives the url for the sound (e.g., CM.Options.GCSoundURL)
 * @param	{string}	sndConfig	The setting in CM.Options that is checked before creating the sound
 * @param	{string}	volConfig	The setting in CM.Options that is checked to determine volume
 * @param	{bool}    forced		Whether the sound should play regardless of settings, used to test the sound
 */
function playCMSound(modName, url, sndConfig, volConfig, forced) {
  if (
    (Game.mods.cookieMonsterFramework.saveData[modName].settings[sndConfig] === 1 || forced) &&
    window.cookieMonsterFrameworkData.isInitializing === false
  ) {
    // eslint-disable-next-line new-cap
    const sound = new Audio(url);
    if (Game.mods.cookieMonsterFramework.saveData[modName].settings.GeneralSound)
      sound.volume =
        (Game.mods.cookieMonsterFramework.saveData[modName].settings[volConfig] / 100) *
        (Game.volume / 100);
    else
      sound.volume = Game.mods.cookieMonsterFramework.saveData[modName].settings[volConfig] / 100;
    sound.play();
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/toggleConfig.js


/**
 * This function toggles options by incrementing them with 1 and handling changes
 * It is called by the onclick event of options of the "bool" type
 * @param 	{string}	modName	      The name of the option
 * @param 	{string}	configName	  The name of the option
 * @param 	{object}	settingsData	Object with data about the settings
 */
function toggleConfig(modName, configName, settingsData) {
  Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] += 1;
  if (
    Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] ===
    settingsData[configName].label.length
  ) {
    Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] = 0;
    if (settingsData[configName].toggle)
      l(`${modName}Options${configName}`).className = 'option off';
  } else l(`${modName}Options${configName}`).className = 'option';

  if (typeof settingsData[configName].func !== 'undefined') {
    settingsData[configName].func();
  }

  saveFramework();
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/toggleConfigKeycode.js


/**
 * This function toggles options by deconstructing the KeyboardEvent
 * It is called by the onclick event of prompts of the "keycode" type
 * @param 	{string}	modName	        The name of the option
 * @param 	{string}	configName	    The name of the option
 * @param   {object}  event           The KeyboardEvent
 */
function toggleConfigKeycode(modName, configName, event) {
  const saveObject = {
    key: event.key,
    altKey: event.altKey,
    ctrlKey: event.ctrlKey,
    shiftKey: event.shiftKey,
    displayName: `${event.shiftKey ? `Shift + ` : ''}${event.altKey ? `Alt + ` : ''}${
      event.ctrlKey ? `Ctrl + ` : ''
    }${event.key}`,
  };
  Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] = saveObject;
  saveFramework();
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/options/toggleConfigVolume.js


/**
 * This function sets the value of the specified volume-option and updates the display in the options menu
 * It is called by the oninput and onchange event of "vol" type options
 * @param 	{string}	modName	    The name of the option
 * @param 	{string}    configName  The name of the option
 */
function toggleConfigVolume(modName, configName) {
  if (l(`slider${modName}${configName}`) !== null) {
    l(`slider${modName}${configName}right`).innerHTML = `${
      l(`slider${modName}${configName}`).value
    }%`;
    Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] = Math.round(
      l(`slider${modName}${configName}`).value,
    );
  }
  saveFramework();
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/menu/listings/createOptionListing.js











/**
 * This function creates an option listing div-object
 * @param 	{string}		modName	          The name of the option
 * @param 	{string}		configName	      The name of the option
 * @param 	{object}		settingsData	    Object with data about the settings
 * @param 	{function}	updateColoursFunc	Function to be called to update colours
 * @param 	{function}	refreshScaleFunc	Function to be called to refresh scale
 * @returns	{object}		div		            The option object
 */
function createOptionsListing(
  modName,
  configName,
  settingsData,
  updateColoursFunc,
  refreshScaleFunc,
) {
  const div = document.createElement('div');
  div.className = 'listing';

  if (Game.mods.cookieMonsterFramework.saveData[modName].settings.FavouriteSettings === 1) {
    div.appendChild(
      createFavouriteStar(
        modName,
        configName,
        Game.mods.cookieMonsterFramework.saveData[modName].favouriteSettings,
      ),
    );
  }

  if (settingsData[configName].type === 'bool') {
    // Create toggle button
    const a = document.createElement('a');
    if (
      settingsData[configName].toggle &&
      Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] === 0
    ) {
      a.className = 'option off';
    } else {
      a.className = 'option';
    }
    a.id = `${modName}Options${configName}`;
    a.onclick = function () {
      toggleConfig(modName, configName, settingsData);
      Game.UpdateMenu();
    };
    a.textContent =
      settingsData[configName].label[
        Game.mods.cookieMonsterFramework.saveData[modName].settings[configName]
      ];
    div.appendChild(a);

    // Create description label
    const label = document.createElement('label');
    label.textContent = settingsData[configName].desc;
    label.style.lineHeight = '1.6';
    div.appendChild(label);
    return div;
  }

  if (settingsData[configName].type === 'vol') {
    const volume = document.createElement('div');

    // Create slider
    volume.className = 'sliderBox';
    const title = document.createElement('div');
    title.style.float = 'left';
    title.innerHTML = settingsData[configName].desc;
    volume.appendChild(title);
    const percent = document.createElement('div');
    percent.id = `slider${modName}${configName}right`;
    percent.style.float = 'right';
    percent.innerHTML = `${Game.mods.cookieMonsterFramework.saveData[modName].settings[configName]}%`;
    volume.appendChild(percent);
    const slider = document.createElement('input');
    slider.className = 'slider';
    slider.id = `slider${modName}${configName}`;
    slider.style.clear = 'both';
    slider.type = 'range';
    slider.min = '0';
    slider.max = '100';
    slider.step = '1';
    slider.value = Game.mods.cookieMonsterFramework.saveData[modName].settings[configName];
    slider.oninput = function () {
      toggleConfigVolume(modName, configName);
      Game.UpdateMenu();
    };
    slider.onchange = function () {
      toggleConfigVolume(modName, configName);
      Game.UpdateMenu();
    };
    volume.appendChild(slider);
    div.appendChild(volume);

    // Create test sound button
    const a = document.createElement('a');
    a.className = 'option';
    a.onclick = function () {
      playCMSound(
        modName,
        Game.mods.cookieMonsterFramework.saveData[modName].settings[
          configName.replace('Volume', 'SoundURL')
        ],
        configName.replace('Volume', 'Sound'),
        configName,
        true,
      );
    };
    a.textContent = 'Test sound';
    div.appendChild(a);
    return div;
  }

  if (settingsData[configName].type === 'url') {
    // Create label
    const span = document.createElement('span');
    span.className = 'option';
    span.textContent = `${settingsData[configName].label} `;
    span.style.lineHeight = '1.6';
    div.appendChild(span);

    // Create input
    const input = document.createElement('input');
    input.id = `${modName}Options${configName}`;
    input.className = 'option';
    input.type = 'text';
    input.readOnly = true;
    input.value = Game.mods.cookieMonsterFramework.saveData[modName].settings[configName];
    input.style.width = '300px';
    div.appendChild(input);
    div.appendChild(document.createTextNode(' '));

    // Create prompt
    const inputPrompt = document.createElement('input');
    inputPrompt.id = `${modName}Options${configName}Prompt`;
    inputPrompt.className = 'option';
    inputPrompt.type = 'text';
    inputPrompt.value = Game.mods.cookieMonsterFramework.saveData[modName].settings[configName];

    const a = document.createElement('a');
    a.className = 'option';
    a.onclick = function () {
      cookieMonsterPrompt(inputPrompt.outerHTML, [
        [
          'Save',
          function () {
            Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] = l(
              `${modName}Options${configName}Prompt`,
            ).value;
            saveFramework();
            Game.ClosePrompt();
            Game.UpdateMenu();
          },
        ],
        [
          'Cancel',
          function () {
            Game.ClosePrompt();
          },
        ],
      ]);
    };
    a.textContent = 'Edit';
    div.appendChild(a);

    // Create description label
    const label = document.createElement('label');
    label.textContent = settingsData[configName].desc;
    label.style.lineHeight = '1.6';
    div.appendChild(label);
    return div;
  }

  if (settingsData[configName].type === 'colour') {
    const innerSpan = document.createElement('span');
    innerSpan.className = 'option';

    // Create input
    const input = document.createElement('input');
    input.id = configName;
    input.style.width = '65px';
    input.value = Game.mods.cookieMonsterFramework.saveData[modName].settings[configName];
    innerSpan.appendChild(input);
    const change = function () {
      Game.mods.cookieMonsterFramework.saveData[modName].settings[this.targetElement.id] =
        this.toHEXString();
      updateColoursFunc();
      saveFramework();
      Game.UpdateMenu();
    };
    // eslint-disable-next-line no-new
    new jscolor(input, { hash: true, position: 'right', onInput: change });

    // Create description label
    const label = document.createElement('label');
    label.textContent = settingsData[configName].desc;
    label.style.lineHeight = '1.6';
    innerSpan.appendChild(label);

    // Create test button for flash colour
    if (configName.includes('Flash')) {
      const a = document.createElement('a');
      a.className = 'option';
      a.onclick = function () {
        createFlash(modName, 3, configName.replace('Colour', ''), true);
      };
      a.textContent = 'Test flash';
      innerSpan.appendChild(a);
    }
    div.appendChild(innerSpan);
    jscolor_default().init();
    return div;
  }

  if (settingsData[configName].type === 'numscale') {
    const span = document.createElement('span');
    span.className = 'option';
    span.textContent = `${settingsData[configName].label} `;
    span.style.lineHeight = '1.6';
    div.appendChild(span);

    // Create input
    const input = document.createElement('input');
    input.id = `${modName}Options${configName}`;
    input.className = 'option';
    input.type = 'number';
    input.value = Game.mods.cookieMonsterFramework.saveData[modName].settings[configName];
    input.min = settingsData[configName].min;
    input.max = settingsData[configName].max;
    input.oninput = function () {
      Game.mods.cookieMonsterFramework.saveData[modName].settings[configName] = this.value;
      saveFramework();
      refreshScaleFunc();
      Game.UpdateMenu();
    };
    div.appendChild(input);
    div.appendChild(document.createTextNode(' '));

    // Create description label
    const label = document.createElement('label');
    label.textContent = settingsData[configName].desc;
    label.style.lineHeight = '1.6';
    div.appendChild(label);
    return div;
  }

  if (settingsData[configName].type === 'keycode') {
    // Create prompt
    const inputPrompt = document.createElement('input');
    inputPrompt.id = `${modName}Options${configName}Prompt`;
    inputPrompt.className = 'option';
    inputPrompt.type = 'text';
    inputPrompt.value =
      Game.mods.cookieMonsterFramework.saveData[modName].settings[configName].displayName;

    // Create toggle button
    const a = document.createElement('a');
    a.className = 'option';
    a.id = `${modName}Options${configName}`;
    a.onclick = function () {
      cookieMonsterPrompt(inputPrompt.outerHTML, []);
      l(`${modName}Options${configName}Prompt`).addEventListener('keyup', (e) => {
        toggleConfigKeycode(modName, configName, e);
        Game.ClosePrompt();
        Game.UpdateMenu();
      });
    };
    a.textContent =
      Game.mods.cookieMonsterFramework.saveData[modName].settings[configName].displayName;
    div.appendChild(a);

    // Create description label
    const label = document.createElement('label');
    label.textContent = settingsData[configName].desc;
    label.style.lineHeight = '1.6';
    div.appendChild(label);
    return div;
  }
  return div;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/menu/listings/createOptionsSubHeader.js


/**
 * This function creates a header-object for the options page
 * @param 	{string}		modName	    The name of the mod
 * @param 	{string}		configName	The name of the Config-group
 * @param 	{string}		text	      The to-be displayed name of the header
 * @returns	{object}		div		      The header object
 */
function createOptionsSubHeader(modName, configName, text) {
  const div = document.createElement('div');
  div.className = 'title';

  div.style.opacity = '0.7';
  div.style.fontSize = '17px';
  div.appendChild(document.createTextNode(`${text} `));

  // Creates the +/- button
  const span = document.createElement('span');
  span.style.cursor = 'pointer';
  span.style.display = 'inline-block';
  span.style.height = '14px';
  span.style.width = '14px';
  span.style.borderRadius = '7px';
  span.style.textAlign = 'center';
  span.style.backgroundColor = '#C0C0C0';
  span.style.color = 'black';
  span.style.fontSize = '13px';
  span.style.verticalAlign = 'middle';
  span.textContent = Game.mods.cookieMonsterFramework.saveData[modName].headers[configName]
    ? '-'
    : '+';
  span.onclick = function () {
    toggleHeader(modName, configName);
    Game.UpdateMenu();
  };
  div.appendChild(span);
  return div;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/data/modInfo.js
/**
 * Short description of the mod
 */
const modDescription = `<a href="https://github.com/CookieMonsterTeam" target="blank">Cookie Monster Team</a>
offers a suite of tools to enhance your game experience.</br>
Originally known from our work on the Cookie Monster add-on we are now expanding and working on new tools within the Cookie Monster Mod Family.</br>
Keep an eye on our GitHub to see future work or use it to report bugs or feature requests!</br>
`;

/* harmony default export */ const modInfo = (modDescription);

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/menuSections/info/createFrameworkInfoMenuSection.js


/**
 * Add things to the Info menu
 * @returns {object}  frameworkInfoDiv  Subsection to which other mods can add their info sections
 */
function createFrameworkInfoMenuSection() {
  const frameworkInfoDiv = document.createElement('div');
  frameworkInfoDiv.className = 'subsection';
  frameworkInfoDiv.id = 'cookieMonsterFrameworkMenuSection';

  const titleDiv = document.createElement('div');
  titleDiv.className = 'title';
  titleDiv.innerHTML = 'Cookie Monster Mod Family';

  const buttonSpan = document.createElement('span');
  buttonSpan.style.cursor = 'pointer';
  buttonSpan.style.display = 'inline-block';
  buttonSpan.style.height = '14px';
  buttonSpan.style.width = '14px';
  buttonSpan.style.borderRadius = '7px';
  buttonSpan.style.textAlign = 'center';
  buttonSpan.style.backgroundColor = '#C0C0C0';
  buttonSpan.style.color = 'black';
  buttonSpan.style.fontSize = '13px';
  buttonSpan.style.verticalAlign = 'middle';
  buttonSpan.textContent = Game.mods.cookieMonsterFramework.saveData.cookieMonsterFramework.headers
    .infoMenu
    ? '-'
    : '+';
  buttonSpan.onclick = function () {
    toggleHeader('cookieMonsterFramework', 'infoMenu');
    Game.UpdateMenu();
  };
  titleDiv.appendChild(buttonSpan);

  frameworkInfoDiv.appendChild(titleDiv);

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterFramework.headers.infoMenu) {
    const descriptionDiv = document.createElement('div');
    descriptionDiv.className = 'listing';
    descriptionDiv.innerHTML = modInfo;
    frameworkInfoDiv.appendChild(descriptionDiv);
  }

  return frameworkInfoDiv;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/menuSections/info/addInfoMenuSection.js

/**
 * Add things to the Info menu
 * The listeners.infoMenu objects contains functions which create <div>'s to add to the menu section
 */
function addInfoMenuSection() {
  const menu = l('menu').children[1];
  menu.insertBefore(createFrameworkInfoMenuSection(), menu.children[1]);

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterFramework.headers.infoMenu) {
    const listeners = Game.mods.cookieMonsterFramework.listeners.infoMenu;
    for (let i = 0; i < listeners.length; i++) {
      l('cookieMonsterFrameworkMenuSection').appendChild(listeners[i]());
    }
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/menuSections/addMenu.js

// import addOptionsMenuSection from './options/addOptionsMenuSection';

/**
 * Call the function to add a Menu based on the current menu
 * @param {MutationObserver}  The observer object that is listening to DOM-changes of id='menu'
 */
function addMenu(_, observer) {
  // Disconnect observer to avoid infinite loop
  observer.disconnect();

  if (Game.onMenu === 'log') {
    addInfoMenuSection();
  } else if (Game.onMenu === 'prefs') {
    // Commented out because this is broken
    // addOptionsMenuSection();
  }

  // Reconnect observer to monitor changes
  observer.observe(document.getElementById('menu'), {
    attributes: true,
    childList: true,
    subtree: true,
  });
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/init/createFlashScreen.js
/**
 * This function creates a white square over the full screen and appends it to l('wrapper')
 */
function createFlashScreen() {
  const WhiteScreen = document.createElement('div');
  WhiteScreen.id = 'CMFlashScreen';
  WhiteScreen.style.width = '100%';
  WhiteScreen.style.height = '100%';
  WhiteScreen.style.backgroundColor = 'white';
  WhiteScreen.style.display = 'none';
  WhiteScreen.style.zIndex = '9999999999';
  WhiteScreen.style.position = 'absolute';
  WhiteScreen.style.pointerEvents = "none";
  l('wrapper').appendChild(WhiteScreen);
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/draw/drawLoop.js
/**
 * Main draw loop
 */
function drawLoop() {}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/data/headers.js
/** This includes all headers of the Cookie Monster Framework and their relevant data */
const headers = { infoMenu: 1, optionsMenu: 1 };
/* harmony default export */ const data_headers = (headers);

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/savingAndLoading/createSaveDataObject.js
/**
 * Creates the save data object to be stored
 * @param   {object}    saveData      The loaded save data
 * @param   {object}    settingsData  The data containing default values of settings
 * @param   {object}    headersData   The data containing default values of headers
 */
function createSaveDataObject(saveData, settingsData, headersData) {
  const modSaveData = {};

  // When a setting is missing (because it is new or modified) these lines add the default value
  const settingsObject = {};
  Object.keys(settingsData).forEach((i) => {
    if (typeof saveData.settings === 'undefined' || typeof saveData.settings[i] === 'undefined') {
      settingsObject[i] = settingsData[i].defaultValue; // eslint-disable-line prefer-destructuring
    } else {
      settingsObject[i] = saveData.settings[i];
    }
  });
  modSaveData.settings = settingsObject;

  // When a header is missing (because it is new or modified) these lines add the default value
  const headersObject = {};
  Object.keys(headersData).forEach((i) => {
    if (typeof saveData.headers === 'undefined' || typeof saveData.headers[i] === 'undefined') {
      headersObject[i] = headersData[i];
    } else {
      headersObject[i] = saveData.headers[i];
    }
  });
  modSaveData.headers = headersObject;

  Object.keys(saveData).forEach((key) => {
    if (key !== 'settings' && key !== 'headers') {
      modSaveData[key] = saveData[key];
    }
  });

  if (typeof modSaveData.favouriteSettings === 'undefined') {
    modSaveData.favouriteSettings = [];
  }
  return modSaveData;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/savingAndLoading/loadMod.js



/**
 * Load the data from a save-file into a mod
 * @param   {string}    modName       The name of the mode to be saved
 * @param   {string}    saveData      JSON-string of the save data
 * @param   {object}    settingsData  The data containing default values of settings
 * @param   {object}    headersData   The data containing default values of headers
 * @param   {Function}  logicLoop     The logic-loop of the mod
 */
function loadMod(modName, saveData, settingsData, headersData, logicLoop) {
  const saveDataObject = JSON.parse(saveData);
  Game.mods.cookieMonsterFramework.saveData[modName] = createSaveDataObject(
    saveDataObject,
    settingsData,
    headersData,
  );
  saveFramework();
  logicLoop();
  Object.keys(Game.mods.cookieMonsterFramework.saveData[modName].settings).forEach((i) => {
    if (typeof settingsData[i].func !== 'undefined') {
      settingsData[i].func();
    }
  });
  Game.UpdateMenu();
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/logic/logicLoop.js
/**
 * Main logic loop
 */
function logicLoop() {}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/data/settings.js
/** This includes all options of the Cookie Monster Framework and their relevant data */
const settings = {};
/* harmony default export */ const data_settings = (settings);

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/load.js





/**
 * This creates a load function to the CM object. Per Game code/comments:
 * "do stuff with the string data you saved previously"
 * @param   {string}    JSON string of save-data
 */
function load(str) {
  loadMod('cookieMonsterFramework', str, data_settings, data_headers, logicLoop);
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/init.js





/**
 * This creates a init function for the CM object. Per Game code/comments:
 * "this function is called as soon as the mod is registered
 * declare hooks here"
 * It starts the further initialization of CookieMonster and registers hooks
 */
function init() {
  // Create Data object in global scope
  window.cookieMonsterFrameworkData = { isInitializing: true };

  // Create MutationObserver for menu sections
  const observer = new MutationObserver(addMenu);
  observer.observe(document.getElementById('menu'), {
    attributes: true,
    childList: true,
    subtree: true,
  });

  // Draw initiaization
  createFlashScreen();

  // Register hooks
  Game.registerHook('draw', drawLoop);

  // Load defaults if there is no previous save
  if (typeof Game.modSaveData.cookieMonsterFramework === 'undefined') {
    load('{}');
  }
  window.cookieMonsterFrameworkData.isInitializing = false;
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/save.js
/**
 * This creates a save function to the CM object. Per Game code/comments:
 * "use this to store persistent data associated with your mod
 * return 'a string to be saved';"
 * @returns {string}    The data to be saved
 */
function save() {
  return JSON.stringify(Game.mods.cookieMonsterFramework.saveData.cookieMonsterFramework);
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/frameworkDataObject/cookieMonsterFramework.js




/** The mod object to be registered with the Modding API */
const cookieMonsterFramework = {
  init: init,
  load: load,
  save: save,
  listeners: {
    infoMenu: [],
    optionsMenu: [],
  },
  saveData: { cookieMonsterFramework: { headers: {}, settings: {} } },
};

/* harmony default export */ const frameworkDataObject_cookieMonsterFramework = (cookieMonsterFramework);

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/init/initModFramework.js


/** Check if Cookie Monster Mod Framework has been loaded yet and if not, does so */
function initModFramework() {
  if (typeof cookieMonsterFrameworkData === 'undefined') {
    Game.registerMod('cookieMonsterFramework', frameworkDataObject_cookieMonsterFramework);
  }
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/init/registerMod.js
/**
 * Adds the mod to the saveData object to store (favourite) settings and headers
 */
function registerMod(modName) {
  Game.mods.cookieMonsterFramework.saveData[modName] = {
    favouriteSettings: [],
    headers: {},
    settings: {},
  };
}

;// ./node_modules/@cookiemonsterteam/cookiemonsterframework/src/index.js



















const initFunctions = {
  initModFramework: initModFramework,
  registerMod: registerMod,
};
const menuFunctions = {
  listings: {
    createInfoListing: createInfoListing,
    createOptionsListing: createOptionsListing,
    createOptionsSubHeader: createOptionsSubHeader,
  },
  createModMenuSection: createModMenuSection,
};

const notificationsFunctions = {
  createFlash: createFlash,
  createNotification: createNotification,
  cookieMonsterPrompt: cookieMonsterPrompt,
  playCMSound: playCMSound,
};

const optionFunctions = {};

const saveAndLoadingFunctions = {
  loadMod: loadMod,
  saveFramework: saveFramework,
};

const settingClasses = {
  SettingColours: SettingColours,
  SettingInputNumber: SettingInputNumber,
  SettingStandard: SettingStandard,
  SettingStandardWithFunc: SettingStandardWithFunc,
  SettingKeycode: SettingKeycode,
  SettingVolume: SettingVolume,
};

;// ./src/Config/Toggles/ToggleWrinklerButtons.js
/**
 * This function updates the display setting of the two objects created by CM.Disp.CreateWrinklerButtons()
 * It is called by changes in CM.Options.WrinklerButtons
 */
function ToggleWrinklerButtons() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerButtons &&
    Game.elderWrath
  ) {
    l('PopAllNormalWrinklerButton').style.display = '';
    l('PopFattestWrinklerButton').style.display = '';
  } else {
    l('PopAllNormalWrinklerButton').style.display = 'none';
    l('PopFattestWrinklerButton').style.display = 'none';
  }
}

;// ./src/Cache/VariablesAndData.js
/* eslint-disable prefer-const */

let CacheDragonAura = 0;
let CacheDragonAura2 = 0;
let CacheLastDragonLevel = 0;
let CacheCostDragonUpgrade = 0;
let CacheLucky = 0;
let CacheLuckyReward = 0;
let CacheLuckyWrathReward = 0;
let CacheLuckyFrenzy = 0;
let CacheLuckyRewardFrenzy = 0;
let CacheLuckyWrathRewardFrenzy = 0;
let CacheConjure = 0;
let CacheConjureReward = 0;
let CacheEdifice = 0;
let CacheEdificeBuilding = 0;
let CacheNoGoldSwitchCookiesPS = 0;
let CacheDragonsFortuneMultAdjustment = 1;
let CacheGoldenCookiesMult = 1;
let CacheWrathCookiesMult = 1;

let CacheHCPerSecond = 0;

let CacheCentEgg = 0;
let CacheSeaSpec = 0;
let CacheLastChoEgg = 0;

let CacheObjects1 = {};
let CacheObjects10 = {};
let CacheObjects100 = {};
let CacheObjectsNextAchievement = {};

let CacheWrinklersTotal = 0;
let CacheWrinklersNormal = 0;
let CacheWrinklersFattest = [0, null];

let CacheCurrWrinklerCPSMult = 0;
let CacheCurrWrinklerCount = 0;

let CacheUpgrades = {};

let CacheAverageClicks = {};
let CacheAverageCookiesFromClicks;

let CacheMissingUpgrades = {};
let CacheMissingUpgradesPrestige = {};
let CacheMissingUpgradesCookies = {};

let CacheChainRequired = 0;
let CacheChainRequiredNext = 0;
let CacheChainMaxReward = [];
let CacheChainWrathRequired = 0;
let CacheChainWrathRequiredNext = 0;
let CacheChainWrathMaxReward = [];
let CacheChainFrenzyRequired = 0;
let CacheChainFrenzyRequiredNext = 0;
let CacheChainFrenzyMaxReward = [];
let CacheChainFrenzyWrathRequired = 0;
let CacheChainFrenzyWrathRequiredNext = 0;
let CacheChainFrenzyWrathMaxReward = [];

let CacheRealCookiesEarned = 0;
let CacheAvgCPSWithChoEgg = 0;

let CacheSpawnedGoldenShimmer = {};
let CacheSeasonPopShimmer = {};

let CacheTimeTillNextPrestige = 0;

/** Stores lowest PP value */
let CacheMinPP = 0;
/** Stores lowest PP value category */
let CacheMinPPBulk = 0;
/** Stores all PP values of all buildings for all buy settings (1, 10, 100) */
let CachePPArray = [];

let CacheGoldenShimmersByID = {};

let CacheSellForChoEgg = 0;

let CookiesDiff;
let WrinkDiff;
let WrinkFattestDiff;
let ChoEggDiff;
let ClicksDiff;

let CacheLastCPSCheck;
let CacheLastCookies;
let CacheLastWrinkCookies;
let CacheLastWrinkFattestCookies;
let CacheLastClicks;

let CacheAverageGainBank;
let CacheAverageGainWrink;
let CacheAverageGainWrinkFattest;
let CacheAverageGainChoEgg;
let CacheAverageCPS;

let CacheLastHeavenlyChips;

let CacheDoRemakeBuildPrices;

let CacheHadBuildAura;

let CacheFarmLevel = -1;
let CacheGardenSoil = -1;
let CacheSupremeIntellect = -1;
let CachePlotChances = [[], [], [], [], [], []];

/** Store the CPS effect of each god if it was put into each slot */
let CacheGods = {
  0: [0, 0, 0],
  1: [0, 0, 0],
  2: [0, 0, 0],
  3: [0, 0, 0],
  4: [0, 0, 0],
  5: [0, 0, 0],
  6: [0, 0, 0],
  7: [0, 0, 0],
  8: [0, 0, 0],
  9: [0, 0, 0],
  10: [0, 0, 0],
};

;// ./src/Sim/VariablesAndData.js
/** All variables used by simulation functions */

let SimObjects = []; // eslint-disable-line prefer-const
let SimUpgrades = []; // eslint-disable-line prefer-const
let SimAchievements = []; // eslint-disable-line prefer-const
let SimBuildingsOwned;
let SimUpgradesOwned;
let SimPledges;
let SimAchievementsOwned;
let SimHeavenlyPower;
let SimPrestige;
let SimDragonAura;
let SimDragonAura2;
let SimGod1;
let SimGod2;
let SimGod3;
let SimDoSims;
let SimEffs;
let SimCookiesPs;
let SimCookiesPsRaw;

;// ./src/Sim/ReplacedGameFunctions/SimAuraMult.js


/**
 * This functions creates functions similarly to Game.auraMult but checks Sim Data instead of Game Data
 */
function SimAuraMult(what) {
  let n = 0;
  if (
    Game.dragonAuras[SimDragonAura].name === what ||
    Game.dragonAuras[SimDragonAura2].name === what
  )
    n = 1;
  if (
    Game.dragonAuras[SimDragonAura].name === 'Reality Bending' ||
    (Game.dragonAuras[SimDragonAura2].name === 'Reality Bending' &&
      Game.dragonLevel >= Game.dragonAurasBN[what].id + 4)
  )
    n += 0.1;
  return n;
}

;// ./src/Sim/ReplacedGameFunctions/SimGetSellMultiplier.js


/**
 * This functions creates functions similarly to Game.getSellMultiplier but checks Sim Data instead of Game Data
 * @returns {number}	giveBack	The multiplier
 */
function SimGetSellMultiplier() {
  let giveBack = 0.25;
  giveBack *= 1 + SimAuraMult('Earth Shatterer');
  return giveBack;
}

;// ./src/Sim/ReplacedGameFunctions/SimEff.js


/**
 * This functions creates functions similarly to Game.Eff but checks Sim Data instead of Game Data
 */
function SimEff(name, def) {
  if (typeof SimEffs[name] === 'undefined') {
    return typeof def === 'undefined' ? 1 : def;
  }
  return SimEffs[name];
}

;// ./src/Sim/ReplacedGameFunctions/SimHas.js


/**
 * This functions creates functions similarly to Game.Has but checks Sim Data instead of Game Data
 */
function SimHas(what) {
  const it = SimUpgrades[what];
  if (it && Game.ascensionMode === 1 && (it.pool === 'prestige' || it.tier === 'fortune')) return 0;
  return it ? it.bought : 0;
}

;// ./src/Sim/ReplacedGameFunctions/SimHasAura.js


/**
 * This functions creates functions similarly to Game.hasAura but checks Sim Data instead of Game Data
 */
function SimHasAura(what) {
  if (
    Game.dragonAuras[SimDragonAura].name === what ||
    Game.dragonAuras[SimDragonAura2].name === what
  ) {
    return true;
  }
  return false;
}

;// ./src/Sim/ReplacedGameFunctions/SimHasGod.js



/**
 * This function checks for the current God level in the sim data
 * It functions similarly to Game.hasGod()
 * @param	{string}	what	Name of the achievement
 */
function SimHasGod(what) {
  if (Game.hasGod) {
    if (SimObjects.Temple.minigame === undefined) {
      SimObjects.Temple.minigame = Game.Objects.Temple.minigame;
    }
    const god = SimObjects.Temple.minigame.gods[what];
    if (SimGod1 === god.id) {
      return 1;
    }
    if (SimGod2 === god.id) {
      if (SimHasAura('Supreme Intellect')) {
        return 1;
      }
      return 2;
    }
    if (SimGod3 === god.id) {
      if (SimHasAura('Supreme Intellect')) {
        return 2;
      }
      return 3;
    }
  }
  return false;
}

;// ./src/Sim/ReplacedGameFunctions/SimModifyBuidlingPrice.js






/**
 * This function calculates the sell price of a building based on current "sim data"
 * @param	{string}	building	Name of the building
 * @param	{number}	price		Current price of building
 * @returns {number}	ModifiedPrice		The modified building price
 */
function SimModifyBuildingPrice(building, price) {
  let ModifiedPrice = price;
  if (SimHas('Season savings')) ModifiedPrice *= 0.99;
  if (SimHas("Santa's dominion")) ModifiedPrice *= 0.99;
  if (SimHas('Faberge egg')) ModifiedPrice *= 0.99;
  if (SimHas('Divine discount')) ModifiedPrice *= 0.99;
  if (SimHas('Fortune #100')) ModifiedPrice *= 0.99;
  // if (SimHasAura('Fierce Hoarder')) ModifiedPrice *= 0.98;
  ModifiedPrice *= 1 - SimAuraMult('Fierce Hoarder') * 0.02;
  if (Game.hasBuff('Everything must go')) ModifiedPrice *= 0.95;
  if (Game.hasBuff('Crafty pixies')) ModifiedPrice *= 0.98;
  if (Game.hasBuff('Nasty goblins')) ModifiedPrice *= 1.02;
  if (building.fortune && SimHas(building.fortune.name)) ModifiedPrice *= 0.93;
  ModifiedPrice *= SimEff('buildingCost');
  if (SimObjects.Temple.minigameLoaded) {
    const godLvl = SimHasGod('creation');
    if (godLvl === 1) ModifiedPrice *= 0.93;
    else if (godLvl === 2) ModifiedPrice *= 0.95;
    else if (godLvl === 3) ModifiedPrice *= 0.98;
  }
  return ModifiedPrice;
}

;// ./src/Sim/SimulationEvents/SellBuilding.js



/**
 * This function calculates the cookies returned for selling a building
 * Base Game does not do this correctly
 * @param	{string}	build		Name of the building
 * @param	{number}	basePrice	Base Price of building
 * @param	{number}	start		Starting amount of building
 * @param	{number}	free		Free amount of building
 * @param	{number}	increase	Increase of building
 * @param	{number}	noSim		1 of 0 depending on if function is called from CM.Sim
 * @returns {number}	moni		Total price gained
 */
function BuildingSell(build, basePrice, start, free, amount, noSim) {
  // Calculate money gains from selling buildings
  // If noSim is set, use Game methods to compute price instead of Sim ones.
  const noSimRes = typeof noSim === 'undefined' ? 0 : noSim;
  let toChange = amount;
  let startingAmount = start;
  let moni = 0;
  if (amount === -1) toChange = startingAmount;
  if (!amount) toChange = Game.buyBulk;
  for (let i = 0; i < toChange; i++) {
    let price = basePrice * Game.priceIncrease ** Math.max(0, startingAmount - free);
    price = noSimRes
      ? Game.modifyBuildingPrice(build, price)
      : SimModifyBuildingPrice(build, price);
    price = Math.ceil(price);
    const giveBack = noSimRes ? build.getSellMultiplier() : SimGetSellMultiplier();
    price = Math.floor(price * giveBack);
    if (startingAmount > 0) {
      moni += price;
      startingAmount -= 1;
    }
  }
  return moni;
}

;// ./src/Data/Scales.js
/** Data related directly to the scales used by Cookie Monster */

/** Array of abbreviations used in the "Metric" scale */
const metric = ['', '', 'M', 'G', 'T', 'P', 'E', 'Z', 'Y'];

/** Array of abbreviations used in the "Short" scale */
const shortScale = [
  '',
  '',
  'M',
  'B',
  'Tr',
  'Quadr',
  'Quint',
  'Sext',
  'Sept',
  'Oct',
  'Non',
  'Dec',
  'Undec',
  'Duodec',
  'Tredec',
  'Quattuordec',
  'Quindec',
  'Sexdec',
  'Septendec',
  'Octodec',
  'Novemdec',
  'Vigint',
  'Unvigint',
  'Duovigint',
  'Trevigint',
  'Quattuorvigint',
];

/** Array of abbreviations used in the "Abbreviated Short" scale */
const shortScaleAbbreviated = [
  '',
  'K',
  'M',
  'B',
  'T',
  'Qa',
  'Qi',
  'Sx',
  'Sp',
  'Oc',
  'No',
  'De',
  'UDe',
  'DDe',
  'TDe',
  'QaDe',
  'QiDe',
  'SxDe',
  'SpDe',
  'ODe',
  'NDe',
  'Vi',
  'UVi',
  'DVi',
  'TVi',
  'QaVi',
  'QiVi',
  'SxVi',
  'SpVi',
  'OVi',
  'NVi',
  'Tr',
  'UTr',
  'DTr',
  'TTr',
  'QaTr',
  'QiTr',
  'SxTr',
  'SpTr',
  'OTr',
  'NTr',
  'Qaa',
  'UQa',
  'DQa',
  'TQa',
  'QaQa',
  'QiQa',
  'SxQa',
  'SpQa',
  'OQa',
  'NQa',
  'Qia',
  'UQi',
  'DQi',
  'TQi',
  'QaQi',
  'QiQi',
  'SxQi',
  'SpQi',
  'OQi',
  'NQi',
  'Sxa',
  'USx',
  'DSx',
  'TSx',
  'QaSx',
  'QiSx',
  'SxSx',
  'SpSx',
  'OSx',
  'NSx',
  'Spa',
  'USp',
  'DSp',
  'TSp',
  'QaSp',
  'QiSp',
  'SxSp',
  'SpSp',
  'OSp',
  'NSp',
  'Oco',
  'UOc',
  'DOc',
  'TOc',
  'QaOc',
  'QiOc',
  'SxOc',
  'SpOc',
  'OOc',
  'NOc',
  'Noa',
  'UNo',
  'DNo',
  'TNo',
  'QaNo',
  'QiNo',
  'SxNo',
  'SpNo',
  'ONo',
  'NNo',
  'Ct',
  'UCt',
];

;// ./src/Main/VariablesAndData.js
let LastModCount;
let TooltipBuildBackup = []; // eslint-disable-line prefer-const
let TooltipLumpBackup;
let TooltipGrimoireBackup = []; // eslint-disable-line prefer-const
let TooltipUpgradeBackup = []; // eslint-disable-line prefer-const
let BackupGrimoireLaunch;
let BackupGrimoireLaunchMod;
let BackupGrimoireDraw;
let HasReplaceNativeGrimoireLaunch;
let HasReplaceNativeGrimoireDraw;
let LoadMinigames;
let BackupFunctions = {}; // eslint-disable-line prefer-const

let LastSeasonPopupState;
let LastTickerFortuneState;
let LastGardenNextStep;
let LastGoldenCookieState;
let LastSpawnedGoldenCookieState;
let LastMagicBarFull;
let CurrSpawnedGoldenCookieState;
let LastWrinklerCount;

/** Stores the date at Game.CalculateGains for God Cyclius
 */
let CycliusDateAtBeginLoop = Date.now(); // eslint-disable-line prefer-const

/** Stores the date at Game.CalculateGains for the Century egg
 */
let CenturyDateAtBeginLoop = Date.now(); // eslint-disable-line prefer-const

;// ./src/Disp/BeautifyAndFormatting/Beautify.js
/** General functions to format or beautify strings */




/**
 * This function returns formats number based on the Scale setting
 * @param	{number}	num		Number to be beautified
 * @param 	{any}		floats 	Used in some scenario's by CM.Backup.Beautify (Game's original function)
 * @param	{number}	forced	Used to force (type 3) in certains cases
 * @returns	{string}			Formatted number
 */
function Beautify_Beautify(num, floats, forced) {
  const decimals =
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleDecimals + 1;
  if (num === Infinity) {
    return 'Infinity';
  }
  if (typeof num === 'undefined') {
    return '0';
  }
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Scale === 0) {
    return BackupFunctions.Beautify(num, floats);
  }
  if (Number.isFinite(num)) {
    if (num < 0) {
      return `-${Beautify_Beautify(Math.abs(num))}`;
    }
    let answer = '';
    if (num === 0) {
      return num.toString();
    }
    if (
      num > 0.001 &&
      num < Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleCutoff
    ) {
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleSeparator)
        answer = num.toLocaleString('nl');
      else answer = num.toLocaleString('en');
      return answer;
    }
    if (
      (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Scale === 4 &&
        !forced) ||
      forced === 4
    ) {
      // Scientific notation, 123456789 => 1.235E+8
      answer = num.toExponential(decimals).toString().replace('e', 'E');
    } else {
      const exponential = num.toExponential().toString();
      const AmountOfTenPowerThree = Math.floor(exponential.slice(exponential.indexOf('e') + 1) / 3);
      answer = (num / Number(`1e${AmountOfTenPowerThree * 3}`)).toFixed(decimals);
      // answer is now "xxx.xx" (e.g., 123456789 would be 123.46)
      if (
        (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Scale === 1 &&
          !forced) ||
        forced === 1
      ) {
        // Metric scale, 123456789 => 123.457 M
        if (num >= 0.01 && num < Number(`1e${metric.length * 3}`)) {
          answer += ` ${metric[AmountOfTenPowerThree]}`;
        } else answer = Beautify_Beautify(num, 0, 4); // If number is too large or little, revert to scientific notation
      } else if (
        (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Scale === 2 &&
          !forced) ||
        forced === 2
      ) {
        // Short scale, 123456789 => 123.457 M
        if (num >= 0.01 && num < Number(`1e${shortScale.length * 3}`)) {
          answer += ` ${shortScale[AmountOfTenPowerThree]}`;
        } else answer = Beautify_Beautify(num, 0, 4); // If number is too large or little, revert to scientific notation
      } else if (
        (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Scale === 3 &&
          !forced) ||
        forced === 3
      ) {
        // Short scale, 123456789 => 123.457 M
        if (num >= 0.01 && num < Number(`1e${shortScaleAbbreviated.length * 3}`)) {
          answer += ` ${shortScaleAbbreviated[AmountOfTenPowerThree]}`;
        } else answer = Beautify_Beautify(num, 0, 4); // If number is too large or little, revert to scientific notation
      } else if (
        (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Scale === 5 &&
          !forced) ||
        forced === 5
      ) {
        // Engineering notation, 123456789 => 123.457E+6
        answer += `E${AmountOfTenPowerThree * 3}`;
      }
    }
    if (answer === '') {
      // eslint-disable-next-line no-console
      console.log(`Could not beautify number with Cookie Monster Beautify: ${num}`);
      answer = BackupFunctions.Beautify(num, floats);
    }
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleSeparator)
      answer = answer.replace('.', ',');
    return answer;
  }
  console.log(`Could not beautify number with Cookie Monster Beautify: ${num}`); // eslint-disable-line no-console
  return BackupFunctions.Beautify(num, floats);
}

;// ./src/Disp/VariablesAndData.js
/**
 * Section: Variables used in Disp functions */

let DispCSS;

/**
 * These are variables used to create DOM object names and id (e.g., 'CMTextTooltip)
 */
const ColourTextPre = 'CMText';
const ColourBackPre = 'CMBack';
const ColourBorderPre = 'CMBorder';

/**
 * These are variables which can be set in the options by the user to standardize colours throughout CookieMonster
 */
const ColourBlue = 'Blue';
const ColourGreen = 'Green';
const ColourYellow = 'Yellow';
const ColourOrange = 'Orange';
const ColourRed = 'Red';
const ColourPurple = 'Purple';
const ColourGray = 'Gray';
const ColourPink = 'Pink';
const ColourBrown = 'Brown';
const ColoursOrdering = [
  ColourBlue,
  ColourGreen,
  ColourYellow,
  ColourOrange,
  ColourRed,
  ColourPurple,
  ColourPink,
  ColourBrown,
  ColourGray,
];

/**
 * This list is used to make some very basic tooltips.
 * It is used by CM.Main.DelayInit() in the call of CM.Disp.CreateSimpleTooltip()
 * @item	{string}	placeholder
 * @item	{string}	text
 * @item	{string}	minWidth
 */
const TooltipText = [
  ['GoldCookTooltipPlaceholder', 'Calculated with Golden Switch off', '200px'],
  [
    'GoldCookDragonsFortuneTooltipPlaceholder',
    'Calculated with Golden Switch off and at least one golden cookie on-screen',
    '240px',
  ],
  [
    'PrestMaxTooltipPlaceholder',
    'The MAX prestige is calculated with the cookies gained from popping all wrinklers with Skruuia god in Diamond slot, selling all stock market goods, selling all buildings with Earth Shatterer and Reality Bending auras, and buying Chocolate egg',
    '320px',
  ],
  [
    'NextPrestTooltipPlaceholder',
    'Calculated with cookies gained from wrinklers and Chocolate egg',
    '200px',
  ],
  [
    'HeavenChipMaxTooltipPlaceholder',
    'The MAX heavenly chips is calculated with the cookies gained from popping all wrinklers with Skruuia god in Diamond slot, selling all stock market goods, selling all buildings with Earth Shatterer and Reality Bending auras, and buying Chocolate egg',
    '330px',
  ],
  [
    'ResetTooltipPlaceholder',
    'The bonus income you would get from new prestige levels unlocked at 100% of its potential and from ascension achievements if you have the same buildings/upgrades after reset',
    '370px',
  ],
  [
    'ChoEggTooltipPlaceholder',
    'The amount of cookies you would get from popping all wrinklers with Skruuia god in Diamond slot, selling all stock market goods, selling all buildings with Earth Shatterer and Reality Bending auras, and then buying Chocolate egg',
    '300px',
  ],
  ['ChainNextLevelPlaceholder', 'Cheated cookies might break this formula', '250px'],
  [
    'AscendAdvisorTooltipPlaceholder',
    'Ascending trades the current run for faster production in every later run: prestige levels (with Legacy) and heavenly upgrades bought with the chips, several at once if affordable. The advisor plans all future ascensions to reach a distant goal as fast as possible, assuming each run grows like this one, and only recommends ascending for at least a 10% speed-up. The forecast range assumes your cookies grow 25% slower or faster than they do now. Wrinklers and the Chocolate egg are counted as if cashed in before ascending.',
    '380px',
  ],
  [
    'FavouriteSettingPlaceholder',
    "Click to set this setting as favourite and show it in 'favourite' settings at the top of the Cookie Monster Settings",
    '250px',
  ],
];
const SimpleTooltipElements = {};

/**
 * These are variables used by the functions that create tooltips for wrinklers
 * See CM.Disp.CheckWrinklerTooltip(), CM.Disp.UpdateWrinklerTooltip() and CM.Main.AddWrinklerAreaDetect()
 */
let TooltipWrinklerArea = 0; // eslint-disable-line prefer-const
let TooltipWrinkler = -1; // eslint-disable-line prefer-const

/**
 * This array is used to store whether a Wrinkler tooltip is being shown or not
 * [i] = 1 means tooltip is being shown, [i] = 0 means hidden
 * It is used by CM.Disp.CheckWrinklerTooltip() and CM.Main.AddWrinklerAreaDetect()
 */
let TooltipWrinklerBeingShown = []; // eslint-disable-line prefer-const

let CMLastAscendState;
let CMSayTime = function () {}; // eslint-disable-line prefer-const

/**
 * These are variables used to create various displays when the game is loaded on the "sell all" screen
 */
let LastTargetBotBar = 1; // eslint-disable-line prefer-const
let LastTargetBuildings = 1; // eslint-disable-line prefer-const
let LastTargetTooltipBuilding = 1; // eslint-disable-line prefer-const

/**
 * These arrays are used in the stats page to show
 * average cookies per {CM.Disp.cookieTimes/CM.Disp.clickTimes} seconds
 */
const CookieTimes = [10, 15, 30, 60, 300, 600, 900, 1800];
const ClickTimes = [1, 5, 10, 15, 30];

/**
 * This array is used to give certain timers specific colours
 */
const BuffColours = {
  Frenzy: ColourYellow,
  'Dragon Harvest': ColourBrown,
  'Elder frenzy': ColourGreen,
  Clot: ColourRed,
  'Click frenzy': ColourBlue,
  Dragonflight: ColourPink,
};

/**
 * This array is used to track GC timers
 */
let GCTimers = {}; // eslint-disable-line prefer-const

/**
 * Used to store the number of cookies to be displayed in the tab-title
 */
let Title = ''; // eslint-disable-line prefer-const

let TooltipPrice;
let TooltipBonusIncome;
let TooltipType;
let TooltipName;
let TooltipBonusMouse;

let LastAscendState;
let LastNumberOfTimers;

/**
 * This stores the names of settings shown in the favourites section
 */
let FavouriteSettings = (/* unused pure expression or super */ null && ([])); // eslint-disable-line prefer-const

;// ./src/Disp/BuildingsUpgrades/Buildings.js





/**
 * Section: Functions related to right column of the screen (buildings/upgrades)

/**
 * This function adjusts some things in the column of buildings.
 * It colours them, helps display the correct sell-price and shuffles the order when CM.Options.SortBuildings is set
 * The function is called by CM.Disp.Draw(), CM.Disp.UpdateColours() & CM.Disp.RefreshScale()
 * And by changes in CM.Options.BuildColour, CM.Options.SortBuild & CM.Data.Config.BulkBuildColour
 */
function UpdateBuildings() {
  let target = Game.buyBulk;
  if (Game.buyMode === 1) {
    LastTargetBuildings = target;
  } else {
    target = LastTargetBuildings;
  }
  if (target === 1) target = CacheObjects1;
  else if (target === 10) target = CacheObjects10;
  else if (target === 100) target = CacheObjects100;

  // Remove colour if applied
  l(`storeBulk1`).style.removeProperty('color');
  l(`storeBulk10`).style.removeProperty('color');
  l(`storeBulk100`).style.removeProperty('color');

  if (Game.buyMode === 1) {
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BuildColour === 1) {
      Object.keys(target).forEach((i) => {
        l(`productPrice${Game.Objects[i].id}`).style.color =
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings[
            `Colour${target[i].colour}`
          ];
      });
      l(`storeBulk${CacheMinPPBulk}`).style.color =
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ColourGreen;
    } else {
      Object.keys(Game.Objects).forEach((i) => {
        l(`productPrice${Game.Objects[i].id}`).style.removeProperty('color');
      });
    }
  } else if (Game.buyMode === -1) {
    Object.keys(CacheObjects1).forEach((i) => {
      const o = Game.Objects[i];
      l(`productPrice${o.id}`).style.color = '';
      /*
       * Fix sell price displayed in the object in the store.
       *
       * The buildings sell price displayed by the game itself (without any mod) is incorrect.
       * The following line of code fixes this issue, and can be safely removed when the game gets fixed.
       *
       * This issue is extensively detailed here: https://github.com/Aktanusa/CookieMonster/issues/359#issuecomment-735658262
       */
      l(`productPrice${o.id}`).innerHTML = Beautify_Beautify(
        BuildingSell(o, o.basePrice, o.amount, o.free, Game.buyBulk, 1),
      );
    });
  }

  // Build array of pointers and sort according to the user's configured sort option.
  // This regulates sorting of buildings.
  let arr;
  if (
    Game.buyMode !== 1 ||
    !Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SortBuildings
  ) {
    arr = Object.keys(CacheObjects1).map((k) => {
      const o = {};
      o.name = k;
      o.id = Game.Objects[k].id;
      return o;
    });
    // Sort using default order.
    arr.sort((a, b) => a.id - b.id);
  } else if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SortBuildings === 1
  ) {
    arr = Object.keys(CacheObjects1).map((k) => {
      const o = {};
      o.name = k;
      o.pp = CacheObjects1[k].pp;
      o.colour = CacheObjects1[k].colour;
      return o;
    });
    // Sort by pp colour group, then by pp.
    arr.sort((a, b) =>
      ColoursOrdering.indexOf(a.colour) === ColoursOrdering.indexOf(b.colour)
        ? a.pp - b.pp
        : ColoursOrdering.indexOf(a.colour) - ColoursOrdering.indexOf(b.colour),
    );
  } else if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SortBuildings === 2
  ) {
    arr = Object.keys(target).map((k) => {
      const o = {};
      o.name = k;
      o.pp = target[k].pp;
      o.colour = target[k].colour;
      return o;
    });
    // Sort by pp colour group, then by pp.
    arr.sort((a, b) =>
      ColoursOrdering.indexOf(a.colour) === ColoursOrdering.indexOf(b.colour)
        ? a.pp - b.pp
        : ColoursOrdering.indexOf(a.colour) - ColoursOrdering.indexOf(b.colour),
    );
  } else if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SortBuildings === 3
  ) {
    arr = Object.keys(CacheObjectsNextAchievement).map((k) => {
      const o = {};
      o.name = k;
      o.id = Game.Objects[k].id;
      o.amountUntilNext = CacheObjectsNextAchievement[k].AmountNeeded;
      o.priceUntilNext = CacheObjectsNextAchievement[k].price;
      return o;
    });
    // First, sort using default order.
    arr.sort((a, b) => a.id - b.id);
    // Sort by price until next achievement.
    // Buildings that aren't within 100 of an achievement are placed at the end, still in
    // default order relative to each other because sort() is guaranteed stable.
    arr.sort(
      (a, b) =>
        (a.amountUntilNext !== 101 ? a.priceUntilNext : Infinity) -
        (b.amountUntilNext !== 101 ? b.priceUntilNext : Infinity),
    );
  }

  // Use array index (+2) as the grid row number.
  // (grid rows are 1-based indexing, and row 1 is the bulk buy/sell options)
  for (let x = 0; x < arr.length; x++) {
    Game.Objects[arr[x].name].l.style.gridRow = `${x + 2}/${x + 2}`;
  }
}

;// ./src/Disp/BuildingsUpgrades/UpdateUpgradeSectionsHeight.js
/**
 * This function toggles the upgrade to be always expanded
 * It is called by a change in CM.Options.ToolWarnPos
 * and upon creation of the warning tooltip by CM.Disp.UpdateTooltipWarnings()
 */
function UpdateUpgradeSectionsHeight() {
  Object.values(document.getElementsByClassName('storeSection')).forEach((section) => {
    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.UpgradesNeverCollapse ||
      section.id === 'products'
    ) {
      section.style.height = 'auto'; // eslint-disable-line no-param-reassign
    } else if (section.id === 'vaultUpgrades') {
      section.style.height = ''; // eslint-disable-line no-param-reassign
      section.style.minHeight = '0px'; // eslint-disable-line no-param-reassign
    } else if (section.id === 'upgrades') {
      section.style.height = ''; // eslint-disable-line no-param-reassign
      if (section.className.includes('hasMenu')) {
        section.style.minHeight = '82px'; // eslint-disable-line no-param-reassign
      } else {
        section.style.minHeight = '60px'; // eslint-disable-line no-param-reassign
      }
    } else {
      section.style.height = ''; // eslint-disable-line no-param-reassign
      section.style.minHeight = '60px'; // eslint-disable-line no-param-reassign
    }
  });
}

;// ./src/Disp/BuildingsUpgrades/Upgrades.js



/**
 * This function adjusts some things in the upgrades section
 * It colours them and shuffles the order when CM.Options.SortBuildings is set
 * The function is called by CM.Disp.Draw(), CM.Disp.ToggleUpgradeBarAndColour & CM.Disp.RefreshScale()
 * And by changes in CM.Options.SortUpgrades
 */
function UpdateUpgrades() {
  // Right after a save is imported the store can hold upgrades that are not cached yet; the next
  // loop caches and draws them
  if (Object.keys(Game.UpgradesInStore).some((i) => !CacheUpgrades[Game.UpgradesInStore[i].name]))
    return;

  // This counts the amount of upgrades for each pp group and updates the Upgrade Bar
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.UpBarColour > 0) {
    let blue = 0;
    let green = 0;
    let yellow = 0;
    let orange = 0;
    let red = 0;
    let purple = 0;
    let gray = 0;

    Object.keys(Game.UpgradesInStore).forEach((i) => {
      const me = Game.UpgradesInStore[i];
      let addedColour = false;
      for (let j = 0; j < l(`upgrade${i}`).childNodes.length; j += 1) {
        if (l(`upgrade${i}`).childNodes[j].className.indexOf(ColourBackPre) !== -1) {
          l(`upgrade${i}`).childNodes[j].className = ColourBackPre + CacheUpgrades[me.name].colour;
          addedColour = true;
          break;
        }
      }
      if (!addedColour) {
        const div = document.createElement('div');
        div.style.width = '10px';
        div.style.height = '10px';
        div.className = ColourBackPre + CacheUpgrades[me.name].colour;
        l(`upgrade${i}`).appendChild(div);
      }
      if (CacheUpgrades[me.name].colour === ColourBlue) blue += 1;
      else if (CacheUpgrades[me.name].colour === ColourGreen) green += 1;
      else if (CacheUpgrades[me.name].colour === ColourYellow) yellow += 1;
      else if (CacheUpgrades[me.name].colour === ColourOrange) orange += 1;
      else if (CacheUpgrades[me.name].colour === ColourRed) red += 1;
      else if (CacheUpgrades[me.name].colour === ColourPurple) purple += 1;
      else if (CacheUpgrades[me.name].colour === ColourGray) gray += 1;
    });

    l('CMUpgradeBarBlue').textContent = blue;
    l('CMUpgradeBarGreen').textContent = green;
    l('CMUpgradeBarYellow').textContent = yellow;
    l('CMUpgradeBarOrange').textContent = orange;
    l('CMUpgradeBarRed').textContent = red;
    l('CMUpgradeBarPurple').textContent = purple;
    l('CMUpgradeBarGray').textContent = gray;
  }

  const arr = [];
  // Build array of pointers, sort by pp, set flex positions
  // This regulates sorting of upgrades
  for (let x = 0; x < Game.UpgradesInStore.length; x += 1) {
    const o = {};
    o.name = Game.UpgradesInStore[x].name;
    o.price = Game.UpgradesInStore[x].basePrice;
    o.pp = CacheUpgrades[o.name].pp;
    o.colour = CacheUpgrades[o.name].colour;
    arr.push(o);
  }

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SortUpgrades) {
    // Sort by pp colour group, then by pp.
    arr.sort((a, b) =>
      ColoursOrdering.indexOf(a.colour) === ColoursOrdering.indexOf(b.colour)
        ? a.pp - b.pp
        : ColoursOrdering.indexOf(a.colour) - ColoursOrdering.indexOf(b.colour),
    );
  } else {
    arr.sort((a, b) => a.price - b.price);
  }

  const nameChecker = function (arr2, upgrade) {
    return arr2.findIndex((e) => e.name === upgrade.name);
  };
  for (let x = 0; x < Game.UpgradesInStore.length; x += 1) {
    l(`upgrade${x}`).style.order = nameChecker(arr, Game.UpgradesInStore[x]) + 1;
  }
}

;// ./src/Data/Moddata.js
/** Data related directly to Cookie Monster */

const VersionMajor = '2.053';
const VersionMinor = '13';

/** Information about Cookie Monster to be displayed in the info section */
const ModDescription = (/* unused pure expression or super */ null && (`<a href="https://github.com/CookieMonsterTeam/CookieMonster" target="blank">Cookie Monster</a>
 offers a wide range of tools and statistics to enhance your game experience.
 It is not a cheat interface – although it does offer helpers for golden cookies and such, everything can be toggled off at will to only leave how much information you want.</br>
 Progess on new updates and all previous release notes can be found on the GitHub page linked above!</br>
 Please also report any bugs you may find over there!</br>
 `));

/** Latest releasenotes of Cookie Monster to be displayed in the info section */
const LatestReleaseNotes = (/* unused pure expression or super */ null && (`Cookie Monster+ (local build based on 2.053.10)</br>
- Version 13 publishes a readable (unminified) build and the full source at github.com/JWKNT/cookie-clicker, installed by a patcher that checks every file</br>
- Version 12 adds Godzamok combos: with Godzamok slotted, autoplay sells and buys back every building type whose round trip pays, every frame, so his click buff keeps growing (income rises thousands of times over), and the Pantheon slots him for it (within seconds of an ascension, or with a sugar lump to refill the worship swaps when they ran out)</br>
- The Grandmapocalypse stage is now chosen by income: with the Elder Pact a pledge costs next to nothing, so autoplay pledges whenever calm (golden cookies, Frenzies on clicks) earns more than wrath and wrinklers, and revokes the covenant the elder achievements leave behind. It bursts wrinklers for "Wrinklesquisher" and "Moistburster" when they are worth the income given up</br>
- Achievements are valued in seconds of play (a share of income times the play still expected); a Born again run for Neverclick and Hardcore starts once they are worth more than its four hours</br>
- The garden breeds new seeds along the wheat chain on a checkerboard (Thumbcorn, Cronerice, Gildmillet, Clover, Golden clover, ...) with the right soil; the Stock Market upgrades its offices and takes loans that end before their interest; sugar lumps go to cursor levels for the first loan and to the Sugar frenzy; fortunes, Santa's helper grandmas, gift codes, dragon petting and a narrow-window ticker click are taken as well</br>
- Version 11 plays the whole game: the Grandmapocalypse (wrath cookies beat golden ones when every cookie is clicked, and wrinklers multiply income about six times), the dragon (trained every run, auras picked by the CpS they add), seasons (Santa, heart biscuits, Easter eggs, reindeer), sugar lumps (minigames first, then building levels), the Pantheon, the Grimoire, permanent upgrade slots, heavenly upgrades for all of these, and achievements that only take an action</br>
- Autoplay: clicks the big cookie (20 per second by default), buys the building or upgrade with the best payback period, clicks golden cookies and reindeer, and ascends at the optimal time (all switchable under Options, Autoplay)</br>
- Ascension Advisor: plans every future ascension with a dynamic program, counting prestige levels, Legacy and the heavenly upgrades the chips can buy (several per ascension); it never recommends an ascension worth less than a 10% speed-up</br>
- Click and golden cookie upgrades are valued at what they bring under autoplay (auto-click rate, golden cookie income), so they are coloured instead of gray and bought when they are the best deal; a "Lucky!" bank is kept only when that pays back faster than buying</br>
- Heavenly chips are spent along one purchase order, most time saved per chip first ((1 - 1/multiplier) / cost, which is provably optimal without parent constraints) with required parents included, which the Ascension Advisor also plans with; auto-ascend buys as many items as the chips cover and saves the rest for the next one</br>
- The auto-buyer judges purchases by what they add to long-run income: click power at the auto-click rate (now for buildings too), multiplied by what the golden cookies autoplay clicks make of production (Frenzies, building specials, cookie storms and Click frenzies), without current buffs. A "Lucky!" bank is only kept back from purchases that pay back slower than banked cookies do, which is now rare</br>
- The "Next buy" countdown uses the income measured over the last ten minutes, as the expected income counts rare jackpots that seldom arrive within minutes</br>
- Timer bar: a "Lucky!" bank row appears while autoplay keeps cookies back for "Lucky!", which explains why an affordable "Next buy" can still be waiting</br>
- Auto-ascend pops normal wrinklers and buys the Chocolate egg before ascending, then reincarnates</br>
- Average CPS is measured on cookies earned, so seconds with a purchase no longer count as zero income</br>
- Exact heavenly chips per second, compact tooltips, combined bank warnings and compact bottom-bar times</br>
- Bugfix: the sell price shown in building tooltips in sell mode was always "1"</br>
- Bugfix: right after the game loaded, the auto-buyer could buy as if there were no "Lucky!" bank (its target was computed before CpS), and in the frame CpS changed it could act on values not yet updated</br>
- Bugfix: the golden cookie timer could show "NaN%" after loading, until the next golden cookie</br>
- Bugfix: importing a save while Cookie Monster was running could stop it loading its settings</br>`));

;// ./src/Disp/BeautifyAndFormatting/FormatTime.js
/**
 * This function returns time as a string depending on TimeFormat setting
 * @param  	{number} 	time		Time to be formatted
 * @param  	{number}	longFormat 	1 or 0
 * @returns	{string}				Formatted time
 */
function FormatTime(time, longFormat) {
  /* eslint-disable no-nested-ternary */
  let formattedTime = time;
  if (time === Infinity) return time;
  if (time < 0) return 'Negative time period';
  formattedTime = Math.ceil(time);
  const y = Math.floor(formattedTime / 31536000);
  const d = Math.floor((formattedTime % 31536000) / 86400);
  const h = Math.floor(((formattedTime % 31536000) % 86400) / 3600);
  const m = Math.floor((((formattedTime % 31536000) % 86400) % 3600) / 60);
  const s = Math.floor((((formattedTime % 31536000) % 86400) % 3600) % 60);
  let str = '';

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimeFormat === 0) {
    if (formattedTime > 777600000) return longFormat ? 'Over 9000 days!' : '>9000d';
    str += y > 0 ? `${y + (longFormat ? (y === 1 ? ' year' : ' years') : 'y')}, ` : '';
    if (str.length > 0 || d > 0)
      str += `${d + (longFormat ? (d === 1 ? ' day' : ' days') : 'd')}, `;
    if (str.length > 0 || h > 0)
      str += `${h + (longFormat ? (h === 1 ? ' hour' : ' hours') : 'h')}, `;
    if (str.length > 0 || m > 0)
      str += `${m + (longFormat ? (m === 1 ? ' minute' : ' minutes') : 'm')}, `;
    str += s + (longFormat ? (s === 1 ? ' second' : ' seconds') : 's');
  } else if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimeFormat === 1) {
    if (formattedTime > 3155760000) return 'XX:XX:XX:XX:XX';
    str += `${(y < 10 ? '0' : '') + y}:`;
    str += `${(d < 10 ? '0' : '') + d}:`;
    str += `${(h < 10 ? '0' : '') + h}:`;
    str += `${(m < 10 ? '0' : '') + m}:`;
    str += (s < 10 ? '0' : '') + s;
  } else {
    // Similar to TimeFormat === 0, but only two most significant components are included.
    if (formattedTime > 777600000) return longFormat ? 'Over 9000 days!' : '>9000d';
    if (y > 0) {
      str += `${y + (longFormat ? (y === 1 ? ' year' : ' years') : 'y')}, `;
      str += `${d + (longFormat ? (d === 1 ? ' day' : ' days') : 'd')}`;
    } else if (d > 0) {
      str += `${d + (longFormat ? (d === 1 ? ' day' : ' days') : 'd')}, `;
      str += `${h + (longFormat ? (h === 1 ? ' hour' : ' hours') : 'h')}`;
    } else if (h > 0) {
      str += `${h + (longFormat ? (h === 1 ? ' hour' : ' hours') : 'h')}, `;
      str += `${m + (longFormat ? (m === 1 ? ' minute' : ' minutes') : 'm')}`;
    } else if (m > 0) {
      str += `${m + (longFormat ? (m === 1 ? ' minute' : ' minutes') : 'm')}, `;
      str += s + (longFormat ? (s === 1 ? ' second' : ' seconds') : 's');
    } else {
      str += s + (longFormat ? (s === 1 ? ' second' : ' seconds') : 's');
    }
  }
  return str;
}

;// ./src/Disp/BeautifyAndFormatting/GetTimeColour.js



/**
 * This function returns the colour to be used for time-strings
 * @param	{number}			time			Time to be coloured
 * @returns {{string, string}}	{text, colour}	Both the formatted time and colour as strings in an array
 */
function GetTimeColour(time) {
  let colour;
  let text;
  if (time <= 0) {
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimeFormat === 1)
      text = '00:00:00:00:00';
    else text = 'Done!';
    colour = ColourGreen;
  } else {
    text = FormatTime(time);
    if (time > 300) colour = ColourRed;
    else if (time > 60) colour = ColourOrange;
    else colour = ColourYellow;
  }
  return { text, colour };
}

;// ./src/Disp/BeautifyAndFormatting/ShortDuration.js
/**
 * Formats a duration with its two most significant units (e.g. "3h 12m"), for compact displays
 * @param	{number}	seconds	Duration
 * @returns	{string}			Formatted duration
 */
function ShortDuration(seconds) {
  if (!Number.isFinite(seconds)) return '∞';
  let rest = Math.max(0, Math.ceil(seconds));
  const units = [
    ['y', 31536000],
    ['d', 86400],
    ['h', 3600],
    ['m', 60],
    ['s', 1],
  ];
  const parts = [];
  for (let i = 0; i < units.length && parts.length < 2; i++) {
    const amount = Math.floor(rest / units[i][1]);
    if (amount > 0 || (parts.length === 0 && i === units.length - 1)) {
      parts.push(`${amount}${units[i][0]}`);
      rest -= amount * units[i][1];
    } else if (parts.length > 0) break;
  }
  return parts.join(' ');
}

;// ./src/Disp/HelperFunctions/GetCPS.js


/**
 * This function returns the cps as either current or average CPS depending on CM.Options.CPSMode
 * @returns	{number}	The average or current cps
 */
function GetCPS() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CPSMode) {
    return CacheAverageCPS;
  }
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 0) {
    return Game.cookiesPs * (1 - Game.cpsSucked);
  }
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 1) {
    return Game.cookiesPs * (CacheCurrWrinklerCPSMult + (1 - CacheCurrWrinklerCount * 0.05));
  }
  if (CacheWrinklersFattest[1] !== null)
    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 2 &&
      Game.wrinklers[CacheWrinklersFattest[1]].type === 1
    ) {
      return (
        Game.cookiesPs *
        ((CacheCurrWrinklerCPSMult * 3) / CacheCurrWrinklerCount +
          (1 - CacheCurrWrinklerCount * 0.05))
      );
    }
  return (
    Game.cookiesPs *
    (CacheCurrWrinklerCPSMult / CacheCurrWrinklerCount + (1 - CacheCurrWrinklerCount * 0.05))
  );
}

;// ./src/Disp/HelperFunctions/GetWrinkConfigBank.js


/**
 * This function returns the total amount stored in the Wrinkler Bank
 * as calculated by  CM.Cache.CacheWrinklers() if CM.Options.CalcWrink is set
 * @returns	{number}	0 or the amount of cookies stored (CM.Cache.WrinklersTotal)
 */
function GetWrinkConfigBank() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 1) {
    return CacheWrinklersTotal;
  }
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 2) {
    return CacheWrinklersFattest[0];
  }
  return 0;
}

;// ./src/Disp/InfoBars/CreateDOMElements.js
/** Functions to create various DOM elements used by the Bars */



/**
 * This function creates an indivudual timer for the timer bar
 * @param	{string}					id					An id to identify the timer
 * @param	{string}					name				The title of the timer
 * @param	[{{string}, {string}}, ...]	bars ([id, colour])	The id and colours of individual parts of the timer
 */
function CreateTimer(id, name, bars) {
  const timerBar = document.createElement('div');
  timerBar.id = id;
  timerBar.style.height = '12px';
  timerBar.style.margin = '0px 10px';
  timerBar.style.position = 'relative';

  const div = document.createElement('div');
  div.style.width = '100%';
  div.style.height = '10px';
  div.style.margin = 'auto';
  div.style.position = 'absolute';
  div.style.left = '0px';
  div.style.top = '0px';
  div.style.right = '0px';
  div.style.bottom = '0px';

  const type = document.createElement('span');
  type.style.display = 'inline-block';
  type.style.textAlign = 'right';
  type.style.fontSize = '10px';
  type.style.width = '108px';
  type.style.marginRight = '5px';
  type.style.verticalAlign = 'text-top';
  type.textContent = name;
  div.appendChild(type);

  for (let i = 0; i < bars.length; i++) {
    const colourBar = document.createElement('span');
    colourBar.id = bars[i].id;
    colourBar.style.display = 'inline-block';
    colourBar.style.height = '10px';
    colourBar.style.verticalAlign = 'text-top';
    colourBar.style.textAlign = 'center';
    if (bars.length - 1 === i) {
      colourBar.style.borderTopRightRadius = '10px';
      colourBar.style.borderBottomRightRadius = '10px';
    }
    if (typeof bars[i].colour !== 'undefined') {
      colourBar.className = ColourBackPre + bars[i].colour;
    }
    div.appendChild(colourBar);
  }

  const timer = document.createElement('span');
  timer.id = `${id}Time`;
  timer.style.marginLeft = '5px';
  timer.style.verticalAlign = 'text-top';
  div.appendChild(timer);

  timerBar.appendChild(div);

  return timerBar;
}

/**
 * This function extends the bottom bar (created by CM.Disp.CreateBotBar) with a column for the given building.
 * @param	{string}	buildingName	Objectname to be added (e.g., "Cursor")
 */
function CreateBotBarBuildingColumn(buildingName) {
  if (l('CMBotBar') !== null) {
    const type = l('CMBotBar').firstChild.firstChild.childNodes[0];
    const bonus = l('CMBotBar').firstChild.firstChild.childNodes[1];
    const pp = l('CMBotBar').firstChild.firstChild.childNodes[2];
    const time = l('CMBotBar').firstChild.firstChild.childNodes[3];

    const i = buildingName;
    const header = type.appendChild(document.createElement('td'));
    header.appendChild(
      document.createTextNode(`${i.indexOf(' ') !== -1 ? i.substring(0, i.indexOf(' ')) : i} (`),
    );

    const span = header.appendChild(document.createElement('span'));
    span.className = ColourTextPre + ColourBlue;

    header.appendChild(document.createTextNode(')'));
    type.lastChild.style.paddingLeft = '8px';
    bonus.appendChild(document.createElement('td'));
    bonus.lastChild.style.paddingLeft = '8px';
    pp.appendChild(document.createElement('td'));
    pp.lastChild.style.paddingLeft = '8px';
    time.appendChild(document.createElement('td'));
    time.lastChild.style.paddingLeft = '2px';
  }
}

;// ./src/Disp/InfoBars/BottomBar.js
/** Functions related to the Bottom Bar */













/**
 * This function creates the bottom bar and appends it to l('wrapper')
 */
function CreateBotBar() {
  const BotBar = document.createElement('div');
  BotBar.id = 'CMBotBar';
  BotBar.style.height = '69px';
  BotBar.style.width = '100%';
  BotBar.style.position = 'absolute';
  BotBar.style.display = 'none';
  BotBar.style.backgroundColor = '#262224';
  BotBar.style.backgroundImage = 'linear-gradient(to bottom, #4d4548, #000000)';
  BotBar.style.borderTop = '1px solid black';
  BotBar.style.overflow = 'auto';
  BotBar.style.textShadow = '-1px 0 black, 0 1px black, 1px 0 black, 0 -1px black';

  const table = BotBar.appendChild(document.createElement('table'));
  table.style.width = '100%';
  table.style.textAlign = 'center';
  table.style.whiteSpace = 'nowrap';
  const tbody = table.appendChild(document.createElement('tbody'));

  const firstCol = function (text, colour) {
    const td = document.createElement('td');
    td.style.textAlign = 'right';
    td.className = ColourTextPre + colour;
    td.textContent = text;
    return td;
  };
  const type = tbody.appendChild(document.createElement('tr'));
  type.style.fontWeight = 'bold';
  type.appendChild(firstCol(`CM+ ${VersionMajor}.${VersionMinor}`, ColourYellow));
  const bonus = tbody.appendChild(document.createElement('tr'));
  bonus.appendChild(firstCol('Bonus Income', ColourBlue));
  const pp = tbody.appendChild(document.createElement('tr'));
  pp.appendChild(firstCol('Payback Period', ColourBlue));
  const time = tbody.appendChild(document.createElement('tr'));
  time.appendChild(firstCol('Time Left', ColourBlue));

  l('wrapper').appendChild(BotBar);

  Object.keys(Game.Objects).forEach((i) => {
    CreateBotBarBuildingColumn(i);
  });
}

/**
 * This function updates the bonus-, pp-, and time-rows in the the bottom bar
 */
function UpdateBotBar() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar === 1 &&
    CacheObjects1 &&
    Game.buyMode === 1
  ) {
    let count = 0;
    Object.keys(CacheObjects1).forEach((i) => {
      let target = Game.buyBulk;
      if (Game.buyMode === 1) {
        LastTargetBotBar = target;
      } else {
        target = LastTargetBotBar;
      }
      if (target === 1) target = CacheObjects1;
      if (target === 10) target = CacheObjects10;
      if (target === 100) target = CacheObjects100;
      count += 1;
      l('CMBotBar').firstChild.firstChild.childNodes[0].childNodes[
        count
      ].childNodes[1].textContent = Game.Objects[i].amount;
      l('CMBotBar').firstChild.firstChild.childNodes[1].childNodes[count].textContent = Beautify_Beautify(
        target[i].bonus,
        2,
      );
      l('CMBotBar').firstChild.firstChild.childNodes[2].childNodes[count].className =
        ColourTextPre + target[i].colour;
      let PPString;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPDisplayTime)
        PPString = FormatTime(Math.round(target[i].pp));
      else PPString = Beautify_Beautify(Math.round(target[i].pp), 2);
      l('CMBotBar').firstChild.firstChild.childNodes[2].childNodes[count].textContent = PPString;
      const secondsLeft =
        (Game.Objects[i].bulkPrice - (Game.cookies + GetWrinkConfigBank())) / GetCPS();
      const timeColour = GetTimeColour(secondsLeft);
      // Two units at most in the default format, so long times fit their column
      if (
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimeFormat === 0 &&
        secondsLeft > 0 &&
        secondsLeft <= 777600000
      )
        timeColour.text = ShortDuration(secondsLeft);
      l('CMBotBar').firstChild.firstChild.childNodes[3].childNodes[count].className =
        ColourTextPre + timeColour.colour;
      if (timeColour.text === 'Done!' && Game.cookies < Game.Objects[i].bulkPrice) {
        l('CMBotBar').firstChild.firstChild.childNodes[3].childNodes[count].textContent =
          `${timeColour.text} (with Wrink)`;
      } else
        l('CMBotBar').firstChild.firstChild.childNodes[3].childNodes[count].textContent =
          timeColour.text;
    });
  }
}

;// ./src/Disp/HelperFunctions/UpdateBackground.js
/**
 * This function sets the size of the background of the full game and the left column
 * depending on whether certain abrs are activated
 * It is called by CM.Disp.UpdateAscendState() and CM.Disp.UpdateBotTimerBarPosition()
 */
function UpdateBackground() {
  Game.Background.canvas.width = Game.Background.canvas.parentNode.offsetWidth;
  Game.Background.canvas.height = Game.Background.canvas.parentNode.offsetHeight;
  Game.LeftBackground.canvas.width = Game.LeftBackground.canvas.parentNode.offsetWidth;
  Game.LeftBackground.canvas.height = Game.LeftBackground.canvas.parentNode.offsetHeight;
  Game.DrawBackground();
}

;// ./src/Config/SpecificToggles.js
/** Called by the "func" of individual settings */



/**
 * This function changes the position of both the bottom and timer bar
 */
function UpdateBotTimerBarPosition() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar === 1 &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1 &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarPos === 1
  ) {
    l('CMBotBar').style.bottom = l('CMTimerBar').style.height;
    l('game').style.bottom = `${Number(l('CMTimerBar').style.height.replace('px', '')) + 70}px`;
  } else if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar === 1) {
    l('CMBotBar').style.bottom = '0px';
    l('game').style.bottom = '70px';
  } else if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1 &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarPos === 1
  ) {
    l('game').style.bottom = l('CMTimerBar').style.height;
  } else {
    // No bars
    l('game').style.bottom = '0px';
  }

  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1 &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarPos === 0
  ) {
    l('sectionLeft').style.top = l('CMTimerBar').style.height;
  } else {
    l('sectionLeft').style.top = '';
  }

  UpdateBackground();
}

/**
 * This function changes the visibility of the timer bar
 */
function ToggleTimerBar() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1)
    l('CMTimerBar').style.display = '';
  else l('CMTimerBar').style.display = 'none';
  UpdateBotTimerBarPosition();
}

/**
 * This function changes the position of the timer bar
 */
function ToggleTimerBarPos() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarPos === 0) {
    l('CMTimerBar').style.width = '30%';
    l('CMTimerBar').style.bottom = '';
    l('game').insertBefore(l('CMTimerBar'), l('sectionLeft'));
  } else {
    l('CMTimerBar').style.width = '100%';
    l('CMTimerBar').style.bottom = '0px';
    l('wrapper').appendChild(l('CMTimerBar'));
  }
  UpdateBotTimerBarPosition();
}

;// ./src/Cache/CPS/GetCPSBuffMult.js
/**
 * This function returns the current CPS buff
 * @returns {number}	mult	The multiplier
 */
function GetCPSBuffMult() {
  let mult = 1;
  Object.keys(Game.buffs).forEach((i) => {
    if (typeof Game.buffs[i].multCpS !== 'undefined') mult *= Game.buffs[i].multCpS;
  });
  return mult;
}

;// ./src/Cache/PP/Godzamok.js
/**
 * Section: Godzamok's "Devastation" buff under autoplay
 *
 * With Godzamok slotted, selling buildings starts a ten-second buff worth +1% click power per building
 * sold (+0.5% in the ruby slot, +0.25% in the jade one), and every sale while it runs adds to it, without
 * limit and without extending it. Selling a building type and buying it straight back in the same frame
 * costs only the gap between the prices: a sale returns a quarter of what the next copy would cost, so
 * selling the top n copies refunds 1.15 x 25% of what buying them back costs. Each building sold adds a
 * hundredth of the auto-clicker's income for the rest of the buff, so cycling pays for every type whose
 * copies are worth less than that, which late in a run is everything but the newest tiers. With the
 * mouse upgrades a click is worth 15% of CpS, so at 20 clicks a second clicking alone earns three times
 * CpS before the buff multiplies it.
 */

/** Click power each building sold adds, by Godzamok's slot (none, diamond, ruby, jade) */
const PER_BUILDING = [0, 0.01, 0.005, 0.0025];
/** Seconds the buff lasts from the first sale */
const BUFF_SECONDS = 10;
/** Milliseconds of each frame autoplay may spend selling and buying back */
const BUDGET_MS = 3;
/** Most passes over the same building types in one frame */
const MAX_PASSES = 4;
/** A cycle must bring in this many times what it costs */
const MARGIN = 2;
/**
 * Never sold: selling the last grandma ends the Elder Pledge and pops every wrinkler (the game's sell
 * hook for grandmas), and "You" is a single copy worth hours of CpS
 */
const NEVER_SELL = ['Grandma', 'You'];

/** Milliseconds one building takes to sell and buy back, measured as autoplay goes */
const GodzamokState = { msPerUnit: 0.0035 };

/**
 * Click power per building sold with Godzamok where it sits now; 0 without him or with the setting off
 * @returns	{number}
 */
function DevastationBonus() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGodzamok || !Game.hasGod || !Game.Objects.Temple.minigameLoaded) return 0;
  return PER_BUILDING[Game.hasGod('ruin') || 0] || 0;
}

/**
 * Cookies to buy back every copy of a building after selling them all, and what the round trip costs
 * once the sale's refund is counted
 * @param	{object}	me	Building
 * @returns	{{rebuy: number, net: number}}
 */
function CycleCost(me) {
  const rebuy = (me.getPrice() * (1 - 1.15 ** -me.amount)) / 0.15;
  return { rebuy, net: rebuy * (1 - 1.15 * me.getSellMultiplier()) };
}

/**
 * Building types worth selling and buying back now: each copy adds bonus x click income for the rest of
 * the buff, which must beat the round trip's cost; the bank must cover buying them back
 * @param	{number}	clickIncome	Auto-click income per second without the buff
 * @param	{number}	seconds	Seconds of buff the sale feeds
 * @param	{number}	bank	Cookies at hand
 * @returns	{object[]}	Buildings
 */
function CycleTypes(clickIncome, seconds, bank) {
  const bonus = DevastationBonus();
  if (!bonus || !(clickIncome > 0) || !(seconds > 0)) return [];
  return Object.keys(Game.Objects)
    .map((name) => Game.Objects[name])
    .filter((me) => {
      if (me.amount < 1 || NEVER_SELL.includes(me.name)) return false;
      const { rebuy, net } = CycleCost(me);
      return bonus * me.amount * clickIncome * seconds > MARGIN * net && rebuy <= bank;
    });
}

/**
 * Average click power multiplier the cycling keeps up. Each frame sells as many buildings as the time
 * budget allows (U), so the buff grows by bonus x U a frame and averages half its final size over its
 * ten seconds
 * @param	{number}	clickIncome	Auto-click income per second without buffs
 * @param	{number}	bank	Cookies at hand
 * @returns	{number}
 */
function GodzamokMultiplier(clickIncome, bank) {
  const bonus = DevastationBonus();
  if (!bonus) return 1;
  const units = CycleTypes(clickIncome, BUFF_SECONDS / 2, bank).reduce(
    (sum, me) => sum + me.amount,
    0,
  );
  if (!units) return 1;
  const perFrame = Math.min(BUDGET_MS / GodzamokState.msPerUnit, MAX_PASSES * units);
  return 1 + (bonus * perFrame * BUFF_SECONDS * Game.fps) / 2;
}

;// ./src/Cache/PP/AutoplayValue.js
/**
 * Section: What upgrades are worth when autoplay clicks the cookie and golden cookies
 *
 * Cookie Monster's CpS simulation values click upgrades and golden cookie upgrades at zero, so they
 * show up gray. With auto-click a click upgrade is worth its extra cookies per click times the click
 * rate, and with auto golden cookies an upgrade that makes golden cookies more frequent or longer is
 * worth the share of income golden cookies bring in.
 */





/** Rough share of golden cookies that turn out "Lucky!" and "Frenzy" respectively */
const LUCKY_SHARE = 0.42;
const FRENZY_SHARE = 0.42;
/** A Frenzy multiplies CpS by 7 for 77 seconds */
const FRENZY_EXTRA_SECONDS = 6 * 77;
/** "Lucky!" pays at most 900 seconds of CpS, when the bank holds at least 6000 seconds */
const LUCKY_MAX_SECONDS = 900;
/** Seconds between golden cookies when the game has not computed its spawn window yet */
const DEFAULT_GOLDEN_INTERVAL = 462;
/**
 * Shares of golden cookie outcomes by Grandmapocalypse stage, when each cookie is a wrath cookie with
 * chance 0, 1/3, 2/3 or 1. Simulated from the game's choice rule (at least 10 buildings, no dragon
 * auras, an 80% chance to avoid repeating the last outcome). Wrath cookies give up Frenzies for clots
 * and ruin, but bring cookie storms and Elder frenzies far more often
 */
const OUTCOME_SHARES = [
  {
    frenzy: 0.4215,
    lucky: 0.4218,
    special: 0.1002,
    clickFrenzy: 0.0397,
    storm: 0.0084,
    chain: 0.0084,
  },
  {
    frenzy: 0.2936,
    lucky: 0.3407,
    special: 0.076,
    debuff: 0.0055,
    clickFrenzy: 0.0324,
    storm: 0.0235,
    chain: 0.0234,
    blood: 0.0167,
    clot: 0.0903,
    ruin: 0.0902,
    cursed: 0.0075,
  },
  {
    frenzy: 0.1565,
    lucky: 0.2801,
    special: 0.0563,
    debuff: 0.0113,
    clickFrenzy: 0.0269,
    storm: 0.039,
    chain: 0.0388,
    blood: 0.0339,
    clot: 0.171,
    ruin: 0.1708,
    cursed: 0.0154,
  },
  {
    lucky: 0.2447,
    special: 0.0411,
    debuff: 0.0176,
    clickFrenzy: 0.0231,
    storm: 0.055,
    chain: 0.0553,
    blood: 0.051,
    clot: 0.2446,
    ruin: 0.2442,
    cursed: 0.0234,
  },
];
/** Gamma(7/6), for the mean golden cookie interval */
const GAMMA_7_6 = 0.927719;

/**
 * Clicks per second of auto-click, 0 when it is off
 * @returns	{number}
 */
function AutoClickRate() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  return settings.AutoClick ? Math.min(Math.max(Number(settings.AutoClickRate) || 0, 0), 50) : 0;
}

/**
 * Average seconds between golden cookies. The spawn chance per frame grows like (k / W)^5 for the k-th
 * frame of a window of W frames, so a cookie survives to fraction x of the window with probability
 * about exp(-W x^6 / 6) and arrives on average at x = Gamma(7/6) (6 / W)^(1/6) of the way in: 24% of the
 * base window, 31% with both frequency upgrades
 * @returns	{number}
 */
function GoldenCookieInterval() {
  const { golden } = Game.shimmerTypes;
  const window = golden.maxTime - golden.minTime;
  const share = window > 0 ? Math.min(GAMMA_7_6 * (6 / window) ** (1 / 6), 1) : 0;
  const interval = (golden.minTime + share * window) / Game.fps;
  return Number.isFinite(interval) && interval > 0 ? interval : DEFAULT_GOLDEN_INTERVAL;
}

/**
 * Grandmapocalypse stage that decides how many golden cookies are wrath cookies (0 while a pledge or
 * the covenant holds; Skruuia makes them all wrath)
 * @returns	{number}	0 to 3
 */
function GrandmapocalypseStage() {
  if (Game.hasGod && Game.hasGod('scorn')) return 3;
  return Math.min(Math.max(Math.round(Number(Game.elderWrath) || 0), 0), 3);
}

/**
 * Extra production from Frenzies as a share of production. A Frenzy multiplies CpS, and the click
 * power that comes from CpS, by 7 for 77 seconds (154 with "Get lucky")
 * @returns	{number}
 */
function FrenzyShare() {
  return (
    (FRENZY_SHARE * FRENZY_EXTRA_SECONDS * (Game.Has('Get lucky') ? 2 : 1)) / GoldenCookieInterval()
  );
}

/**
 * Income from golden cookies as a share of other income, 0 when auto golden cookies is off
 * @param	{number}	income	Cookies per second without golden cookies
 * @param	{number}	bank	Cookies in the bank, which caps "Lucky!" rewards
 * @returns	{{frenzy: number, lucky: number, total: number}}
 */
function GoldenShares(income, bank) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGolden) return { frenzy: 0, lucky: 0, total: 0 };
  const interval = GoldenCookieInterval();
  const frenzy = FrenzyShare();
  const lucky =
    (LUCKY_SHARE *
      Math.min(LUCKY_MAX_SECONDS, (0.15 * bank) / Math.max(income, 1e-9)) *
      CacheGoldenCookiesMult) /
    interval;
  return { frenzy, lucky, total: frenzy + lucky };
}

/**
 * Seconds for a banked cookie, below the "Lucky!" bank, to pay itself back through golden cookies:
 * "Lucky!" pays 15% of the bank and a cookie chain about a fifth of it, while a wrath "Ruin" takes 5%
 * @returns	{number}
 */
function LuckyBankPayback() {
  const shares = OUTCOME_SHARES[GrandmapocalypseStage()];
  const g = CacheGoldenCookiesMult;
  const perCookie =
    (shares.lucky || 0) * 0.15 * g + (shares.chain || 0) * 0.215 * g - (shares.ruin || 0) * 0.05;
  return perCookie > 0 ? GoldenCookieInterval() / perCookie : Infinity;
}

/**
 * Extra income from a store upgrade about golden cookies
 * @param	{string}	name	Upgrade name
 * @param	{number}	income	Cookies per second
 * @param	{number}	bank	Cookies in the bank
 * @returns	{number}	Cookies per second
 */
function GoldenUpgradeValue(name, income, bank) {
  const shares = GoldenShares(income, bank);
  // "Golden cookies appear twice as often", so golden cookie income doubles
  if (name === 'Lucky day' || name === 'Serendipity') return income * shares.total;
  // "Golden cookie effects last twice as long": Frenzies double, "Lucky!" does not
  if (name === 'Get lucky') return income * shares.frenzy;
  if (name === 'Golden goose egg') return 0.05 * income * shares.total;
  return 0;
}

/**
 * Value of a store upgrade under autoplay: its CpS, its click power at the auto-click rate and its
 * golden cookie effect
 * @param	{string}	name	Upgrade name
 * @param	{object}	cached	The upgrade's entry in CM.Cache.Upgrades ({bonus, bonusMouse})
 * @param	{number}	income	Cookies per second
 * @param	{number}	bank	Cookies in the bank
 * @returns	{number}	Cookies per second
 */
function AutoplayUpgradeValue(name, cached, income, bank) {
  return (
    (cached.bonus || 0) +
    AutoClickRate() * Math.max(cached.bonusMouse || 0, 0) +
    GoldenUpgradeValue(name, income, bank)
  );
}

/**
 * Income used by autoplay: CpS (without wrinkler losses) plus auto-click income
 * @returns	{number}	Cookies per second
 */
function AutoplayIncome() {
  return Math.max(
    Game.cookiesPs * (1 - Game.cpsSucked) + AutoClickRate() * Game.computedMouseCps,
    1e-9,
  );
}

/**
 * Product of the current buffs' multipliers on click power (Click frenzy, Dragonflight, ...)
 * @returns	{number}
 */
function ClickBuffMult() {
  let mult = 1;
  Object.keys(Game.buffs).forEach((i) => {
    if (typeof Game.buffs[i].multClick !== 'undefined') mult *= Game.buffs[i].multClick;
  });
  return mult;
}

/**
 * How much longer golden cookie effects last, as the game computes it when one is clicked
 * @returns	{number}
 */
function EffectDuration() {
  let d = 1;
  if (Game.Has('Get lucky')) d *= 2;
  if (Game.Has('Lasting fortune')) d *= 1.1;
  ['Lucky digit', 'Lucky number', 'Green yeast digestives', 'Lucky payout'].forEach((name) => {
    if (Game.Has(name)) d *= 1.01;
  });
  if (Game.auraMult) d *= 1 + Game.auraMult('Epoch Manipulator') * 0.05;
  if (Game.eff) d *= Game.eff('goldenCookieEffDur');
  if (Game.hasGod) d *= [1, 1.07, 1.05, 1.02][Game.hasGod('decadence') || 0];
  return d;
}

/**
 * Wrinklers autoplay expects to keep: the most the game allows once the Grandmapocalypse has started,
 * otherwise those already there
 * @returns	{number}
 */
function ExpectedWrinklers() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (settings.AutoElder && Game.elderWrath > 0 && Game.getWrinklersMax)
    return Game.getWrinklersMax();
  return (Game.wrinklers || []).filter((me) => me.phase === 2).length;
}

/**
 * Long-run multiplier n wrinklers put on CpS. Each one digests the whole withered share s = n / 20 of
 * CpS and returns it x1.1 (plus bonuses) when popped, so they turn 1 into 1 - s + s * n * 1.1: about 6
 * with 10 wrinklers
 * @param	{number}	n	Wrinklers
 * @returns	{number}
 */
function WrinklerFactor(n) {
  if (!(n > 0)) return 1;
  const guts = Game.auraMult ? Game.auraMult('Dragon Guts') : 0;
  const s = Math.min(1, n * 0.05 * (Game.eff ? Game.eff('wrinklerEat') : 1) * (1 + guts * 0.2));
  let back = 1.1 * (1 + guts * 0.2);
  if (Game.Has('Sacrilegious corruption')) back *= 1.05;
  if (Game.Has('Wrinklerspawn')) back *= 1.05;
  if (Game.hasGod) back *= [1, 1.15, 1.1, 1.05][Game.hasGod('scorn') || 0];
  return 1 - s + s * n * back;
}

/**
 * Average extra seconds of CpS, of click income and of direct payout each golden cookie outcome brings
 * (d: effect duration, n: mean count of building types with at least 10, r: clicks per second, g: golden
 * cookie gains). Buffs multiply CpS and the click power that comes from it; wrinklers digest buffed CpS
 * too, so buff seconds are worth W each, while payouts arrive directly
 * @returns	{object}	{outcome: {buff, click, direct}}
 */
function OutcomeEffects(d, n, r, g) {
  const debuff = -30 * d * (1 - 10 / (10 + n));
  return {
    frenzy: { buff: 6 * 77 * d, click: 6 * 77 * d, direct: 0 },
    special: { buff: 3 * n * d, click: 3 * n * d, direct: 0 },
    debuff: { buff: debuff, click: debuff, direct: 0 },
    blood: { buff: 665 * 6 * d, click: 665 * 6 * d, direct: 0 },
    clot: { buff: -0.5 * 66 * d, click: -0.5 * 66 * d, direct: 0 },
    clickFrenzy: { buff: 0, click: 776 * 13 * d, direct: 0 },
    // Cookie storms drop about 15 golden cookies a second, each worth 1 to 7 minutes of CpS
    storm: { buff: 0, click: 0, direct: 105 * d * 240 * g },
    // A cursed finger halts production; each click pays 10 seconds of CpS instead
    cursed: { buff: -10 * d, click: -10 * d, direct: r * (10 * d) ** 2 },
  };
}

/**
 * Golden cookie model for the auto-buyer: the long-run multipliers golden cookies put on one cookie per
 * second of CpS and of click income (below the "Lucky!" bank, where "Lucky!", chains and ruin depend on
 * the bank rather than on production), and the golden cookie income in all
 * @param	{number}	bank	Cookies in the bank
 * @param	{number}	cps	CpS without buffs
 * @param	{number}	clicks	Auto-click income without buffs
 * @param	{number}	W	Wrinkler factor
 * @param	{number}	intervalMult	Factor on the golden cookie interval (to try out other gods)
 * @param	{number}	stage	Grandmapocalypse stage, which sets the mix of outcomes
 * @returns	{{growth: {cps: number, click: number}, golden: number, lasting: number}}
 */
function GoldenModel(bank, cps, clicks, W, intervalMult, stage) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGolden) return { growth: { cps: W, click: 1 }, golden: 0, lasting: 0 };
  const tall = Object.keys(Game.Objects)
    .map((name) => Game.Objects[name].amount)
    .filter((amount) => amount >= 10);
  const n = tall.length ? tall.reduce((sum, amount) => sum + amount, 0) / tall.length : 0;
  const g = CacheGoldenCookiesMult;
  const effects = OutcomeEffects(EffectDuration(), n, AutoClickRate(), g);
  const shares = OUTCOME_SHARES[stage];
  const interval = GoldenCookieInterval() * intervalMult;
  let cpsGain = 0;
  let clickGain = 0;
  Object.keys(effects).forEach((outcome) => {
    const share = shares[outcome] || 0;
    cpsGain += (share * (effects[outcome].buff * W + effects[outcome].direct)) / interval;
    clickGain += (share * effects[outcome].click) / interval;
  });
  const lasting = cpsGain * cps + clickGain * clicks;
  const bankGain =
    ((shares.lucky || 0) * Math.min(0.15 * bank, 900 * cps) * g +
      (shares.chain || 0) * 0.43 * Math.min(21600 * cps, 0.5 * bank) * g -
      (shares.ruin || 0) * Math.min(0.05 * bank, 600 * cps)) /
    interval;
  return {
    growth: { cps: W + cpsGain, click: 1 + clickGain },
    golden: lasting + bankGain,
    lasting,
  };
}

/**
 * The economy the auto-buyer judges purchases by, with current buffs taken out (otherwise a Frenzy
 * would make every purchase look seven times better for 77 seconds): CpS, auto-click income, the
 * long-run multipliers golden cookies and wrinklers put on each, the golden cookie income and the
 * expected total income, which fills the bank. Click income includes the average "Devastation" buff
 * that selling and buying back buildings keeps up when Godzamok is slotted
 * @param	{number}	bank	Cookies in the bank
 * @param	{number}	[intervalMult]	Factor on the golden cookie interval (to try out other gods)
 * @param	{{stage: number, W: number}}	[assume]	Grandmapocalypse stage and wrinkler factor to assume
 * instead of the current ones (to compare stages)
 * @returns	{{cpsBuff: number, clickBuff: number, devastation: number, cps: number, clicks: number, W: number, growth: {cps: number, click: number}, golden: number, lasting: number, income: number}}
 */
function AutoplayEconomy(bank, intervalMult = 1, assume = {}) {
  const cpsBuff = GetCPSBuffMult() || 1;
  const clickBuff = ClickBuffMult() || 1;
  const cps = Game.cookiesPs / cpsBuff;
  const baseClicks = (AutoClickRate() * Game.computedMouseCps) / (cpsBuff * clickBuff);
  const devastation = GodzamokMultiplier(baseClicks, bank);
  const clicks = baseClicks * devastation;
  const W = assume.W !== undefined ? assume.W : WrinklerFactor(ExpectedWrinklers());
  const stage = assume.stage !== undefined ? assume.stage : GrandmapocalypseStage();
  const model = GoldenModel(bank, cps, clicks, W, intervalMult, stage);
  return {
    cpsBuff,
    clickBuff,
    devastation,
    cps,
    clicks,
    W,
    growth: model.growth,
    golden: model.golden,
    lasting: model.lasting,
    income: Math.max(cps * W + clicks + model.golden, 1e-9),
  };
}

/**
 * What a golden cookie upgrade adds to income under autoplay: twice as frequent doubles golden cookie
 * income, twice as long doubles every effect but "Lucky!", chains and ruin
 * @param	{string}	name	Upgrade name
 * @param	{object}	economy	From AutoplayEconomy()
 * @returns	{number}	Cookies per second
 */
function GoldenEffectValue(name, economy) {
  if (name === 'Lucky day' || name === 'Serendipity') return economy.golden;
  if (name === 'Golden goose egg') return 0.05 * economy.golden;
  if (name === 'Get lucky') return economy.lasting;
  return 0;
}

/**
 * What a purchase adds to long-run income under autoplay, in cookies per second: its CpS and its click
 * power at the auto-click rate, without current buffs and multiplied by what golden cookies and
 * wrinklers make of each, plus its effect on golden cookies. This is the gain to compare with the
 * "Lucky!" return of keeping the cookies in the bank
 * @param	{string}	name	Building or upgrade name
 * @param	{object}	cached	Its entry in CM.Cache ({bonus, bonusMouse})
 * @param	{object}	economy	From AutoplayEconomy()
 * @returns	{number}	Cookies per second
 */
function LongRunValue(name, cached, economy) {
  const cps = (cached.bonus || 0) / economy.cpsBuff;
  const clicks =
    (AutoClickRate() * Math.max(cached.bonusMouse || 0, 0) * (economy.devastation || 1)) /
    (economy.cpsBuff * economy.clickBuff);
  return (
    cps * economy.growth.cps + clicks * economy.growth.click + GoldenEffectValue(name, economy)
  );
}

/** Kitten upgrades and how much of the milk each turns into CpS, from the game's CpS formula */
const KITTENS = {
  'Kitten helpers': 0.1,
  'Kitten workers': 0.125,
  'Kitten engineers': 0.15,
  'Kitten overseers': 0.175,
  'Kitten managers': 0.2,
  'Kitten accountants': 0.2,
  'Kitten specialists': 0.2,
  'Kitten experts': 0.2,
  'Kitten consultants': 0.2,
  'Kitten assistants to the regional manager': 0.175,
  'Kitten marketeers': 0.15,
  'Kitten analysts': 0.125,
  'Kitten executives': 0.115,
  'Kitten admins': 0.11,
  'Kitten strategists': 0.105,
  'Kitten angels': 0.1,
  'Fortune #103': 0.05,
};

/**
 * How strongly milk counts, as in the game's CpS formula (Santa's milk and cookies, Breath of Milk,
 * Mokalsium and the milk effect of garden plants)
 * @returns	{number}
 */
function MilkMultiplier() {
  let m = 1;
  if (Game.Has("Santa's milk and cookies")) m *= 1.05;
  if (Game.auraMult) m *= 1 + Game.auraMult('Breath of Milk') * 0.05;
  if (Game.hasGod) m *= [1, 1.1, 1.05, 1.03][Game.hasGod('mother') || 0];
  if (Game.eff) m *= Game.eff('milk');
  return m;
}

/**
 * Share of CpS one more achievement adds: it raises milk by 0.04, and each owned kitten multiplies CpS
 * by 1 + k * milk * m, so CpS grows by the factor prod (1 + k m (milk + 0.04)) / (1 + k m milk)
 * @returns	{number}
 */
function AchievementValue() {
  const m = MilkMultiplier();
  const milk = Game.milkProgress || 0;
  let ratio = 1;
  Object.keys(KITTENS).forEach((name) => {
    if (Game.Has(name))
      ratio *= (1 + KITTENS[name] * m * (milk + 0.04)) / (1 + KITTENS[name] * m * milk);
  });
  return ratio - 1;
}

/**
 * Seconds of play still to come, for valuing permanent gains: as long again as the save has been played
 * so far (with no other information, the median remaining lifetime of something equals its age), and at
 * least an hour
 * @returns	{number}
 */
function PlayHorizon() {
  const played = (Date.now() - (Number(Game.fullDate) || Date.now())) / 1000;
  return Math.max(played, 3600);
}

/**
 * What achievements are worth in seconds of play. A run at speed S retraces the same trajectory S times
 * faster, so a permanent gain of a share x of income makes all future play x faster: over a horizon H it
 * is worth x H seconds, to be weighed against seconds of delay (cookies spent at income I cost
 * cookies / I seconds)
 * @param	{number}	[count]	Achievements
 * @returns	{number}	Seconds
 */
function AchievementWorth(count = 1) {
  return count * AchievementValue() * PlayHorizon();
}

/**
 * Factor of milk a kitten upgrade turns into CpS (0 for anything else)
 * @param	{string}	name	Upgrade name
 * @returns	{number}
 */
function KittenMilkFactor(name) {
  return KITTENS[name] || 0;
}

;// ./src/Main/Autoplay/AutoSeasons.js
/**
 * Section: seasons under autoplay
 *
 * Seasonal upgrades are lost at every ascension, so each run collects them again:
 * - Christmas: A festive hat, then Santa's 14 levels (each unlocks a gift such as Santa's legacy, +3% CpS
 *   per level; the last one unlocks Santa's dominion, +20%)
 * - Valentine's day: the 7 heart biscuits (+2% CpS each), each unlocked by buying the previous one, in one
 *   short visit once they are cheap
 * - Easter: eggs drop from 10% of golden cookies; the run stays until 7 eggs while "Egging on" is missing
 * The rest of the run is spent in Christmas: reindeer pay one or two minutes of CpS each and drop
 * Christmas cookies, more than any other season brings. Switching costs a minute of CpS (x1.5 per switch in
 * a run). These actions are worth far more than they cost, so the auto-buyer keeps back the cookies for the
 * next one whenever it costs at most RESERVE_SECONDS of income. Without the Season switcher only the natural
 * season is used.
 */



/** Eggs to collect in a run while "Egging on" (7 eggs) is missing */
const EGG_GOAL = 7;
/**
 * Seconds of income the auto-buyer keeps back for the next seasonal action: early in a run purchases pay
 * back within minutes, so a longer pause would cost more than the season brings
 */
const RESERVE_SECONDS = 60;

/**
 * Cookies the auto-buyer should keep for the next seasonal action (0 when there is none or it is not cheap)
 * @item	{number}	reserve
 */
const SeasonState = { reserve: 0 };

/**
 * Upgrades in a list that are unlocked or owned this run
 * @param	{string[]}	names	Upgrade names
 * @returns	{number}
 */
function CountUnlocked(names) {
  return (names || []).filter((name) => Game.HasUnlocked(name) || Game.Has(name)).length;
}

/**
 * Cookies to buy every heart biscuit not owned yet
 * @returns	{number}
 */
function HeartsCost() {
  return (Game.heartDrops || [])
    .filter((name) => !Game.Has(name))
    .reduce((sum, name) => sum + Game.Upgrades[name].getPrice(), 0);
}

/**
 * Price of switching to a season (0 if already in it, Infinity if it cannot be triggered)
 * @param	{string}	season	Season key
 * @returns	{number}
 */
function SwitchCost(season) {
  if (Game.season === season) return 0;
  if (!Game.Has('Season switcher') || !Game.seasons[season]) return Infinity;
  const trigger = Game.Upgrades[Game.seasons[season].trigger];
  return trigger && trigger.unlocked && !trigger.bought ? trigger.getPrice() : Infinity;
}

/**
 * The season the run should be in and the cookies its next action needs
 * @param	{number}	cheap	Cookies counted as cheap (RESERVE_SECONDS of income)
 * @returns	{{season: string, cost: number}}
 */
function SeasonPlan(cheap) {
  if (!Game.Has('A festive hat') || Game.santaLevel < 14) {
    const switching = SwitchCost('christmas');
    if (switching > 0) return { season: 'christmas', cost: switching };
    if (!Game.Has('A festive hat')) return { season: 'christmas', cost: 25 };
    return { season: 'christmas', cost: (Game.santaLevel + 1) ** (Game.santaLevel + 1) };
  }
  const hearts = HeartsCost();
  if (hearts > 0 && hearts + SwitchCost('valentines') <= cheap)
    return { season: 'valentines', cost: hearts + SwitchCost('valentines') };
  const eggs = CountUnlocked(Game.eggDrops) + CountUnlocked(Game.rareEggDrops);
  if (!Game.HasAchiev('Egging on') && eggs < EGG_GOAL)
    return { season: 'easter', cost: SwitchCost('easter') };
  return { season: 'christmas', cost: SwitchCost('christmas') };
}

/**
 * Buys what the current season offers: the festive hat and Santa's levels at Christmas, the heart
 * biscuits on Valentine's day (other seasonal cookies and eggs are left to the auto-buyer)
 * @returns	{boolean}	Whether something was bought
 */
function SeasonPurchases() {
  if (Game.season === 'christmas') {
    const hat = Game.Upgrades['A festive hat'];
    if (hat && hat.unlocked && !hat.bought && Game.cookies >= hat.getPrice()) {
      hat.buy();
      return true;
    }
    if (Game.Has('A festive hat') && Game.santaLevel < 14) {
      const level = Game.santaLevel;
      Game.UpgradeSanta();
      if (Game.specialTab) Game.ToggleSpecialMenu(0);
      return Game.santaLevel !== level;
    }
  }
  if (Game.season === 'valentines') {
    const heart = (Game.heartDrops || [])
      .map((name) => Game.Upgrades[name])
      .find((me) => me.unlocked && !me.bought);
    if (heart && Game.cookies >= heart.getPrice()) {
      heart.buy();
      return true;
    }
  }
  return false;
}

/**
 * Switches seasons, buys seasonal upgrades and sets the reserve the auto-buyer keeps for them
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoSeasons() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  SeasonState.reserve = 0;
  if (!settings.AutoSeasons || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  // Production without golden cookies: the expected income counts rare jackpots, too much early in a run
  const economy = AutoplayEconomy(Game.cookies);
  const cheap = (economy.cps * economy.W + economy.clicks) * RESERVE_SECONDS;
  const plan = SeasonPlan(cheap);
  if (Number.isFinite(plan.cost) && plan.cost <= cheap) SeasonState.reserve = plan.cost;
  if (SeasonPurchases() || !Game.Has('Season switcher') || plan.season === Game.season) return;
  const trigger = Game.Upgrades[Game.seasons[plan.season].trigger];
  if (trigger && trigger.unlocked && !trigger.bought && Game.cookies >= trigger.getPrice())
    trigger.buy();
}

;// ./src/Main/Autoplay/Challenge.js
/**
 * Section: the "Born again" challenge run
 *
 * "Neverclick" (1 million cookies baked with at most 15 clicks) and "Hardcore" (1 billion baked without
 * buying an upgrade) only count in a Born again run, which starts from nothing: no prestige, heavenly
 * upgrades, sugar lumps or minigames. A simulation of such a run (buildings only, golden cookies
 * clicked, the 15 clicks spent on the first cursor) reaches 1 million in about 41 minutes and 1 billion
 * in about 3.8 hours. The run earns nothing worth having, so it delays all later play by its length, and
 * autoplay starts one when the achievements are worth more than that (see AchievementWorth). It then
 * plays the run within the rules (no clicks past 15 until "Neverclick", no upgrades until "Hardcore")
 * and ascends as soon as both are won, back into a normal run.
 */



/** Seconds a Born again run takes to reach each achievement, rounded up from the simulation */
const NEVERCLICK_SECONDS = 0.75 * 3600;
const HARDCORE_SECONDS = 4 * 3600;
/** Clicks "Neverclick" allows */
const NEVERCLICK_CLICKS = 15;
/** Give up on a run that takes this many times longer than expected */
const TIMEOUT_FACTOR = 2;

/**
 * Whether this is a Born again run
 * @returns	{boolean}
 */
function ChallengeRun() {
  return Game.ascensionMode === 1;
}

/**
 * The challenge achievements not won yet
 * @returns	{string[]}
 */
function Missing() {
  return ['Neverclick', 'Hardcore'].filter((name) => !Game.HasAchiev(name));
}

/**
 * Seconds a Born again run needs for what is missing (Hardcore's billion comes after Neverclick's
 * million, so one run gets both)
 * @returns	{number}
 */
function ChallengeSeconds() {
  return Game.HasAchiev('Hardcore') ? NEVERCLICK_SECONDS : HARDCORE_SECONDS;
}

/**
 * Whether the next run should be a Born again run: the missing achievements are worth more seconds of
 * play than the run takes. Not twice in a row, in case a run timed out
 * @param	{boolean}	lastWasChallenge	Whether the run just ended was one
 * @returns	{boolean}
 */
function ChallengeDue(lastWasChallenge) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const missing = Missing().length;
  if (!settings.AutoChallenge || !missing || lastWasChallenge) return false;
  return ChallengeSeconds() <= AchievementWorth(missing);
}

/**
 * Whether the big cookie may be clicked: in a Born again run, only 15 times until "Neverclick"
 * @returns	{boolean}
 */
function ClicksAllowed() {
  return !(
    ChallengeRun() &&
    !Game.HasAchiev('Neverclick') &&
    Game.cookieClicks >= NEVERCLICK_CLICKS
  );
}

/**
 * Whether upgrades may be bought: in a Born again run, not until "Hardcore"
 * @returns	{boolean}
 */
function UpgradesAllowed() {
  return !(ChallengeRun() && !Game.HasAchiev('Hardcore'));
}

/**
 * Whether the Born again run is over: both achievements won, or it took far longer than expected
 * @returns	{boolean}
 */
function ChallengeDone() {
  if (!ChallengeRun()) return false;
  const elapsed = (Date.now() - Game.startDate) / 1000;
  return !Missing().length || elapsed > TIMEOUT_FACTOR * ChallengeSeconds();
}

;// ./src/Main/Autoplay/AutoBuy.js






/** Upgrade pools the buyer never touches: switches, heavenly upgrades and unused content */
const SkippedPools = ['toggle', 'prestige', 'debug', 'dungeon', 'shadow', 'unused'];
/** The Chocolate egg is worth most right before ascending, which the ascension routine handles */
const SkippedUpgrades = ['Chocolate egg'];
/** Seconds of measured income behind the countdown, and the least history it needs */
const ETA_WINDOW = 600;
const ETA_MIN_HISTORY = 60;

/**
 * The purchase the buyer is saving for, shown in the timer bar
 * @item	{object|null}	next	{name, price, payback, reserve, reason, spendable, eta} or null when nothing is planned;
 * reserve is what is kept back from this purchase (0 when none): the "Lucky!" bank (reason 'lucky') or
 * cookies for the next seasonal action (reason 'season'); spendable is the bank above it
 */
const AutoBuyState = { next: null };

/**
 * Buys the building or upgrade with the best payback period as soon as it is affordable
 * Purchases are valued by what they add to long-run income under autoplay: CpS and click power at the
 * auto-click rate, without current buffs and grown by Frenzies, plus golden cookie effects. Cookies are
 * kept for a maximum "Lucky!" reward whenever a banked cookie pays itself back through "Lucky!" faster
 * than the purchase would
 */
function AutoBuy() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  // CpS changed this frame and Cookie Monster recomputes its values after autoplay runs, so values
  // and the "Lucky!" bank are stale until the next tick
  if (SimDoSims && settings.AutoBuy) return;
  AutoBuyState.next = null;
  if (!settings.AutoBuy || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  if (Game.buyMode !== 1) return; // The store is in sell mode

  const bank = Game.cookies;
  const economy = AutoplayEconomy(bank);
  const bankPayback = LuckyBankPayback();
  const keepLucky = settings.AutoGolden && settings.AutoBuyLuckyBank;
  const seasonReserve = settings.AutoSeasons ? SeasonState.reserve : 0;
  if (keepLucky && !(CacheLucky > 0) && Game.cookiesPs > 0) return; // "Lucky!" bank not known yet

  let best = null;
  const consider = (name, price, value, buy) => {
    if (!(value > 0) || !Number.isFinite(price)) return;
    const payback = price / value;
    const lucky = keepLucky && payback > bankPayback ? CacheLucky : 0;
    const reserve = Math.max(lucky, seasonReserve);
    let reason = '';
    if (reserve > 0) reason = lucky >= seasonReserve ? 'lucky' : 'season';
    const pp = Math.max(price - (bank - reserve), 0) / economy.income + payback;
    if (best === null || pp < best.pp) best = { name, price, payback, pp, reserve, reason, buy };
  };

  Object.keys(Game.Objects).forEach((name) => {
    const me = Game.Objects[name];
    if (me.locked || !CacheObjects1[name]) return;
    consider(name, me.getPrice(), LongRunValue(name, CacheObjects1[name], economy), () =>
      me.buy(1),
    );
  });
  Game.UpgradesInStore.forEach((me) => {
    if (
      !UpgradesAllowed() ||
      SkippedPools.includes(me.pool) ||
      SkippedUpgrades.includes(me.name) ||
      me.clickFunction ||
      me.priceLumps > 0
    )
      return;
    const value = LongRunValue(me.name, CacheUpgrades[me.name] || {}, economy);
    consider(me.dname || me.name, me.getPrice(), value, () => me.buy());
  });
  if (best === null) return;

  // The countdown uses income measured in this run: the expected income counts rare jackpots (cookie
  // storms, Click frenzies) that seldom land within a few minutes
  const history = Math.min(ETA_WINDOW, Math.floor((Date.now() - Game.startDate) / 1000));
  const measured =
    CookiesDiff && history >= ETA_MIN_HISTORY && CookiesDiff.queue.length >= history
      ? CookiesDiff.calcAverage(history)
      : 0;
  const etaIncome = Math.max(measured, economy.cps + economy.clicks, 1e-9);
  const spendable = bank - best.reserve;
  AutoBuyState.next = {
    name: best.name,
    price: best.price,
    payback: best.payback,
    reserve: best.reserve,
    reason: best.reason,
    spendable,
    eta: Math.max(best.price - spendable, 0) / etaIncome,
  };
  if (best.price <= spendable) best.buy();
}

;// ./src/Cache/FillCMDCache.js
/**
 * Insert the provided values into `window.CookieMonsterData.Cache`.
 *
 * The initial 'Cache' is dropped from the name, so e.g. `CacheWrinklersTotal`
 * becomes `window.CookieMonsterData.Cache.WrinklersTotal`.
 */
function FillCMDCache(caches) {
  if (!('Cache' in window.CookieMonsterData)) {
    window.CookieMonsterData.Cache = {};
  }

  Object.keys(caches).forEach((name) => {
    const exportName = name.replace(/^Cache/, '');

    if (typeof caches[name] === 'undefined') {
      window.CookieMonsterData.Cache[exportName] = undefined;
    } else {
      // Passing through JSON ensures that no references are retained.
      window.CookieMonsterData.Cache[exportName] = JSON.parse(JSON.stringify(caches[name]));
    }
  });
}

;// ./src/Cache/Stats/AscensionMath.js
/**
 * Section: Pure functions for optimal ascension timing
 *
 * Model
 * -----
 * Prestige is P = cbrt(cookiesAllTime / 1e12). Every run benefits from a production speed S(P) that
 * depends on the prestige at its start: S = (heavenly upgrade multipliers) × (1 + 0.01·h·floor(P)),
 * where h is the prestige power (it needs the Legacy heavenly upgrade, after which the "Heavenly ..."
 * store upgrades restore it every run). Heavenly chips accumulate over ascensions, so one ascension
 * can buy several heavenly upgrades at once; S(P) assumes the chips available at P are spent along a
 * fixed purchase order (best production gain per chip first), saving up for the next item.
 *
 * Because S multiplies every source of income, a run at speed S retraces the same trajectory S times
 * faster: cookiesBaked(t; S) = F(S·t). F follows the current run: a fresh run rebuilds to the cookies
 * baked so far (convexly, exponent at least 1.5), then grows like the current run does now, as a power
 * law with exponent β = cps × run time / cookies baked this run.
 *
 * Optimal stopping
 * ----------------
 * Ascending is a trade: it restarts the run in exchange for a faster speed in every later run. The best
 * moment minimises the total time to reach a distant prestige goal, which is solved exactly with a
 * dynamic program over the prestige at which each future ascension happens:
 *
 *     V(P) = min over P' > P of [ runTime(P → P') + τ + V(P') ]
 *
 * and the current run continues to whichever target P* minimises remainingTime(P*) + τ + V(P*).
 * Ascending now is optimal when that target is the current prestige. In the late game (S ∝ P) this
 * reproduces the closed-form optimum of multiplying all-time cookies by v per run, with
 * (β/3)(v−1)/v = (1 − v^(−γ/3))/γ and γ = 3/β − 1 (β = 2 → v ≈ 7.9, β = 3 → v ≈ 16.8); in the early game,
 * where prestige barely changes production, it correctly keeps baking.
 */

const COOKIES_PER_PRESTIGE_CUBED = 1e12;
const BETA_MIN = 0.3;
const BETA_MAX = 12;
/**
 * Lowest growth exponent assumed while a fresh run rebuilds to the current run's cookies: every run
 * starts from zero CpS and grows convexly, even when the current run's income has stalled
 */
const BETA_REBUILD_MIN = 1.5;
/**
 * Smallest speed gain worth an ascension. Guards against a stalled run (for example while nothing is
 * being bought) making a restart for a percent or two look worthwhile
 */
const MIN_SPEED_GAIN = 0.1;

/**
 * Prestige gained by baking `cookiesRun` on top of `cookiesReset`, without catastrophic cancellation
 * when the run is tiny compared to the all-time total.
 * @param	{number}	cookiesReset	All-time cookies before this run
 * @param	{number}	cookiesRun		Cookies baked this run
 * @returns	{number}					Continuous (unfloored) prestige gain
 */
function PrestigeGain(cookiesReset, cookiesRun) {
  if (!(cookiesRun > 0)) return 0;
  if (!(cookiesReset > 0)) return Math.cbrt(cookiesRun / COOKIES_PER_PRESTIGE_CUBED);
  const prestigeBefore = Math.cbrt(cookiesReset / COOKIES_PER_PRESTIGE_CUBED);
  return prestigeBefore * Math.expm1(Math.log1p(cookiesRun / cookiesReset) / 3);
}

/**
 * Builds the speed of a run as a function of the total prestige at its start
 * @param	{object}	heavenly
 * @param	{number}	heavenly.levels			Prestige levels owned now (Game.prestige)
 * @param	{number}	heavenly.chips			Unspent heavenly chips now
 * @param	{boolean}	heavenly.hasLegacy		Whether Legacy is owned
 * @param	{number}	heavenly.power			Prestige power h once Legacy is owned
 * @param	{number}	heavenly.ownedMult		Product of the modelled heavenly multipliers already owned
 * @param	{{cost: number, mult: number}[]}	heavenly.upgrades	Purchase order of upgrades not owned yet; cost includes the parents they still need
 * @returns	{{speedAt: function, currentSpeed: number}}	speedAt(P) for a run starting at prestige P, and the speed of the current run
 */
function SpeedModel(heavenly) {
  const { upgrades } = heavenly;
  const speedAt = (prestige) => {
    const levels = Math.max(Math.floor(prestige), heavenly.levels);
    let chips = heavenly.chips + levels - heavenly.levels;
    let { hasLegacy } = heavenly;
    if (!hasLegacy && chips >= 1) {
      hasLegacy = true;
      chips -= 1;
    }
    let mult = heavenly.ownedMult;
    if (hasLegacy) {
      for (let i = 0; i < upgrades.length && upgrades[i].cost <= chips; i++) {
        chips -= upgrades[i].cost;
        mult *= upgrades[i].mult;
      }
    }
    return mult * (1 + 0.01 * (hasLegacy ? heavenly.power : 0) * levels);
  };
  const currentSpeed =
    heavenly.ownedMult * (1 + 0.01 * (heavenly.hasLegacy ? heavenly.power : 0) * heavenly.levels);
  return { speedAt, currentSpeed };
}

/** Future runs considered by the planner span this many times the current run's length */
const HORIZON_RUN_LENGTHS = 1e4;
/** Phase-shifted goals whose decisions are combined, to cancel end-of-horizon effects */
const GOAL_PHASES = 5;

/**
 * Solves the dynamic program for one goal
 * @param	{object}	run		Precomputed run quantities (see PlanAscension)
 * @param	{number}	goalFactor	All-time cookies at the goal, relative to now
 * @returns	{{index: number, factors: number[], speeds: number[], remaining: number, total: number, ascendNowTotal: number}}
 */
function SolveForGoal(run, goalFactor) {
  const { allTime, cookiesRun, runTime, overhead, beta, betaRebuild, speed, gridSize } = run;
  const prestigeAt = (factor) => Math.cbrt((allTime * factor) / COOKIES_PER_PRESTIGE_CUBED);

  // Grid of all-time cookies relative to now: log-spaced, plus every whole prestige level while levels
  // are coarse enough to matter (each one is +1% of prestige power)
  const factors = [];
  for (let i = 0; i <= gridSize; i++) factors.push(goalFactor ** (i / gridSize));
  const prestigeGoal = prestigeAt(goalFactor);
  for (let level = Math.floor(prestigeAt(1)) + 1; level < Math.min(prestigeGoal, 400); level++) {
    factors.push((level ** 3 * COOKIES_PER_PRESTIGE_CUBED) / allTime);
  }
  factors.sort((a, b) => a - b);
  const n = factors.length;
  const speeds = factors.map((factor) => speed.speedAt(prestigeAt(factor)));

  // Time from the start of a run at the current speed until it has baked `cookies`: rebuilding to the
  // current run's cookies, then growing like the current run
  const timeToBake = (cookies) =>
    runTime * (cookies / cookiesRun) ** (1 / (cookies <= cookiesRun ? betaRebuild : beta));
  const runDuration = (cookies, s) => timeToBake(cookies) * (speed.currentSpeed / s);
  const remainingAt = (j) =>
    j === 0 ? 0 : timeToBake(cookiesRun + allTime * (factors[j] - 1)) - runTime;

  // value[i]: shortest time from a fresh run at factors[i] to the goal
  const value = new Array(n).fill(0);
  for (let i = n - 2; i >= 0; i--) {
    let best = Infinity;
    for (let j = i + 1; j < n; j++) {
      const t =
        runDuration(allTime * (factors[j] - factors[i]), speeds[i]) +
        (j === n - 1 ? 0 : overhead) +
        value[j];
      if (t < best) best = t;
    }
    value[i] = best;
  }

  // The current run: keep baking until factors[j], then ascend (-1: no worthwhile ascension in sight)
  let index = -1;
  let total = Infinity;
  for (let j = 0; j < n - 1; j++) {
    if (speeds[j] / speed.currentSpeed - 1 >= MIN_SPEED_GAIN) {
      const t = remainingAt(j) + overhead + value[j];
      if (t < total) {
        total = t;
        index = j;
      }
    }
  }
  return {
    index,
    factors,
    speeds,
    remaining: index === -1 ? Infinity : remainingAt(index),
    total,
    ascendNowTotal: overhead + value[0],
  };
}

/**
 * Plans the current run's ascension
 * @param	{object}	state
 * @param	{number}	state.cookiesReset	All-time cookies before this run
 * @param	{number}	state.cookiesRun	Cookies this run would convert into prestige
 * @param	{number}	state.income		Effective income (cookies per second)
 * @param	{number}	state.runTime		Seconds since the run started
 * @param	{number}	state.overhead		Seconds lost per ascension (τ)
 * @param	{{speedAt: function, currentSpeed: number}}	speed	From SpeedModel()
 * @param	{object}	[options]
 * @param	{number}	[options.gridSize]	Log-spaced grid points of the dynamic program
 * @returns	{object}	plan
 */
function PlanAscension(state, speed, options = {}) {
  const { cookiesReset, cookiesRun, income, runTime, overhead } = state;
  if (!(cookiesRun > 0) || !(income > 0) || !(runTime > 0)) return { applicable: false };

  const beta = Math.min(Math.max((income * runTime) / cookiesRun, BETA_MIN), BETA_MAX);
  const allTime = cookiesReset + cookiesRun;
  const run = {
    allTime,
    cookiesRun,
    runTime,
    overhead,
    beta,
    betaRebuild: Math.max(beta, BETA_REBUILD_MIN),
    speed,
    gridSize: options.gridSize || 400,
  };

  // The horizon covers what the current run's growth could bake in HORIZON_RUN_LENGTHS run lengths,
  // which keeps every duration within a range where the hour-scale decision is not lost to rounding
  const horizon = 1 + (cookiesRun / allTime) * HORIZON_RUN_LENGTHS ** beta;
  const solutions = [];
  for (let k = 0; k < GOAL_PHASES; k++) {
    solutions.push(SolveForGoal(run, horizon * 10 ** (k / GOAL_PHASES)));
  }
  const targetOf = (solution) =>
    solution.index === -1 ? Infinity : solution.factors[solution.index];
  solutions.sort((a, b) => targetOf(a) - targetOf(b));
  const solution = solutions[Math.floor(GOAL_PHASES / 2)];
  const { index, factors, speeds, remaining } = solution;

  const prestigeAt = (factor) => Math.cbrt((allTime * factor) / COOKIES_PER_PRESTIGE_CUBED);
  const levelsBefore = Math.floor(Math.cbrt(cookiesReset / COOKIES_PER_PRESTIGE_CUBED));
  const prestigeNow = prestigeAt(1);
  const found = index !== -1;
  const targetPrestige = found ? prestigeAt(factors[index]) : Infinity;

  // Remaining time to the same target if the growth exponent is 25% lower or higher than measured
  const ratio = found ? (cookiesRun + allTime * (factors[index] - 1)) / cookiesRun : Infinity;
  const remainingWithBeta = (b) => {
    if (!found) return Infinity;
    return index === 0 ? 0 : runTime * (ratio ** (1 / b) - 1);
  };

  let costOfAscendingNow = null;
  if (index === 0) costOfAscendingNow = 0;
  else if (found) costOfAscendingNow = Math.max(0, solution.ascendNowTotal - solution.total);
  return {
    applicable: true,
    ascendNow: index === 0,
    targetFound: found,
    beta,
    prestigeNow,
    targetPrestige,
    remaining,
    remainingSlow: remainingWithBeta(beta * 0.8),
    remainingFast: remainingWithBeta(beta * 1.25),
    levelsNow: Math.floor(prestigeNow) - levelsBefore,
    levelsAtTarget: found ? Math.floor(targetPrestige) - levelsBefore : Infinity,
    speedGainNow: speeds[0] / speed.currentSpeed - 1,
    speedGainAtTarget: found ? speeds[index] / speed.currentSpeed - 1 : 0,
    // Extra time to the goal if you ascended now instead of at the target (null: not worth it at all)
    costOfAscendingNow,
    readiness: found ? runTime / (runTime + remaining) : 0,
  };
}

/**
 * The all-time-cookies multiplier per run that is optimal in a pure power-law late game (S ∝ P).
 * Used to validate the dynamic program.
 * @param	{number}	beta	Growth exponent of cookies baked versus run time
 * @returns	{number}	v such that ascending when all-time cookies grew v-fold is optimal
 */
function OptimalRunMultiplier(beta) {
  const b = Math.min(Math.max(beta, 0.5), 20);
  const g = 3 / b - 1;
  const f = (v) =>
    (b * (v - 1)) / (3 * v) -
    (Math.abs(g) < 1e-9 ? Math.log(v) / 3 : -Math.expm1((-g / 3) * Math.log(v)) / g);
  let lo = 1 + 1e-6;
  let hi = 2;
  while (f(hi) > 0 && hi < 1e12) {
    lo = hi;
    hi *= 2;
  }
  for (let i = 0; i < 100; i++) {
    const mid = Math.sqrt(lo * hi);
    if (f(mid) > 0) lo = mid;
    else hi = mid;
  }
  return Math.sqrt(lo * hi);
}

;// ./src/Cache/Stats/HeavenlyPlan.js
/** Section: Which heavenly upgrades to buy with heavenly chips, and in which order */




/** "Lucky ..." heavenly upgrades: +1% prestige effect on CpS and +1% golden cookie effect duration */
const luckyUpgrade = (ctx) => 1.01 * (1 + 0.01 * ctx.golden.frenzy);

/**
 * Estimated production multiplier of each heavenly upgrade worth chips under autoplay, given
 * ctx = {clickShare, golden: {frenzy, lucky, total}, autoplay} (income shares of clicks and golden
 * cookies, and which autoplay systems are on).
 * Upgrades not listed are only bought as parents of listed ones: cosmetics, the golden switch and the
 * shimmering veil (they turn off or break on golden cookies), offline production, fortunes, gifts,
 * petting the dragon and the sugar frenzy.
 */
const HeavenlyUpgradeValues = {
  'Heavenly cookies': () => 1.1,
  'Wrinkly cookies': () => 1.1,
  'Sugar crystal cookies': () => 1.05,
  Heralds: () => 1 + 0.01 * Game.heralds,
  'Kitten angels': () => 1 + 0.1 * Game.milkProgress,
  'Halo gloves': (ctx) => 1 + 0.1 * ctx.clickShare,
  'Heavenly luck': (ctx) => 1 + 0.05 * ctx.golden.total,
  'Lasting fortune': (ctx) => 1 + 0.1 * ctx.golden.frenzy,
  'Lucky digit': luckyUpgrade,
  'Lucky number': luckyUpgrade,
  'Lucky payout': luckyUpgrade,
  'Distilled essence of redoubled luck': (ctx) => 1 + 0.01 * ctx.golden.total,
  'Sugar baking': () => 1 + 0.01 * Math.min(Game.lumps, 100),
  // Estimates for upgrades that work through cheaper or extra store upgrades
  'Divine discount': () => 1.01,
  'Divine sales': () => 1.005,
  'Divine bakeries': () => 1.03,
  'Synergies Vol. I': () => 1.05,
  'Synergies Vol. II': () => 1.05,
  'Tin of british tea biscuits': () => 1.02,
  'Box of macarons': () => 1.02,
  'Box of brand biscuits': () => 1.02,
  'Tin of butter cookies': () => 1.02,
  'Box of maybe cookies': () => 1.02,
  'Box of not cookies': () => 1.02,
  'Box of pastries': () => 1.02,
  'Starter kit': () => 1.005,
  'Starter kitchen': () => 1.005,
  'Persistent memory': () => 1.01,
  // Systems that autoplay runs every ascension (estimates)
  // The dragon reaches Radiant Appetite (x2) once 100 of the first 14 buildings can be sacrificed
  'How to bake your dragon': (ctx) => (ctx.autoplay.dragon ? 1.8 : 1),
  // Christmas (Santa's levels and gifts), Easter eggs, Valentine's and Halloween cookies every run
  'Season switcher': (ctx) => (ctx.autoplay.seasons ? 1.3 : 1),
  // A kitten kept from the start of every run; later slots hold weaker upgrades
  'Permanent upgrade slot I': () => 1.12,
  'Permanent upgrade slot II': () => 1.08,
  'Permanent upgrade slot III': () => 1.06,
  'Permanent upgrade slot IV': () => 1.04,
  'Permanent upgrade slot V': () => 1.03,
  // Wrinklers: respawn five times as fast, two more of them (about 1.4x their income), +5% returns
  'Unholy bait': (ctx) => (ctx.autoplay.elder ? 1.05 : 1),
  'Elder spice': (ctx) => (ctx.autoplay.elder ? 1.25 : 1),
  'Sacrilegious corruption': (ctx) => (ctx.autoplay.elder ? 1.04 : 1),
  'Five-finger discount': () => 1.01,
  Starspawn: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Starsnow: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Starterror: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Starlove: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Startrade: (ctx) => (ctx.autoplay.seasons ? 1.005 : 1),
  Keepsakes: (ctx) => (ctx.autoplay.seasons ? 1.02 : 1),
  // Sending yourself a gift and redeeming it earns "No time like the present": one more achievement
  'Wrapping paper': (ctx) => (ctx.autoplay.achievements ? 1.02 : 1),
};

/**
 * Shares of income from clicks and golden cookies that value the heavenly upgrades. "Lucky!" is
 * counted at its maximum, as autoplay keeps the bank for it when that pays
 * @param	{number}	income		Cookies per second
 * @param	{number}	clickIncome	Cookies per second from auto-click
 * @returns	{{clickShare: number, golden: object, autoplay: object}}
 */
function HeavenlyContext(income, clickIncome) {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  return {
    clickShare: income > 0 ? clickIncome / income : 0,
    golden: GoldenShares(income, CacheLucky),
    autoplay: {
      dragon: !!settings.AutoDragon,
      seasons: !!settings.AutoSeasons,
      elder: !!settings.AutoElder,
      achievements: !!settings.AutoAchievements,
    },
  };
}

/**
 * The unowned upgrades needed to own `upgrade`, parents first (the ascension screen only sells an
 * upgrade once all its parents are owned)
 * @param	{object}	upgrade	A heavenly upgrade
 * @param	{object}	planned	Names already owned or planned
 * @returns	{object[]|null}	The upgrades to buy in order, or null if one of them is unavailable
 */
function Bundle(upgrade, planned) {
  const bundle = [];
  const seen = {};
  const visit = (me) => {
    if (!me || me === -1 || me.bought || planned[me.name] || seen[me.name]) return true;
    if (me.showIf && !me.showIf()) return false;
    seen[me.name] = true;
    for (let i = 0; i < me.parents.length; i++) {
      if (!visit(me.parents[i])) return false;
    }
    bundle.push(me);
    return true;
  };
  return visit(upgrade) ? bundle : null;
}

/**
 * Orders the valued heavenly upgrades by time saved per chip: repeatedly picks the upgrade whose
 * bundle (the upgrade plus the parents it still needs, valued together) has the largest
 * (1 - 1/multiplier) / cost. When earning chips takes time inversely proportional to the speed, swapping
 * two adjacent purchases changes the total time by exactly the difference of this index, so sorting by
 * it is optimal (Smith's rule for multiplicative speed-ups). Legacy is left out; it costs one chip and
 * is always bought first.
 * The ascension planner assumes chips are spent along this order, saving up for the next item, and
 * auto-ascend spends them exactly that way.
 * @param	{object}	ctx	From HeavenlyContext()
 * @returns	{{name: string, bundle: object[], cost: number, mult: number}[]}
 */
function HeavenlyPurchaseOrder(ctx) {
  const planned = { Legacy: true };
  const valueOf = (me) =>
    HeavenlyUpgradeValues[me.name] ? HeavenlyUpgradeValues[me.name](ctx) : 1;
  const candidates = Object.keys(HeavenlyUpgradeValues)
    .map((name) => Game.Upgrades[name])
    .filter((me) => me && !me.bought);
  const order = [];
  for (;;) {
    let best = null;
    candidates.forEach((me) => {
      if (planned[me.name]) return;
      const bundle = Bundle(me, planned);
      if (bundle === null) return;
      const mult = bundle.reduce((product, it) => product * valueOf(it), 1);
      if (!(mult > 1)) return;
      const cost = bundle.reduce((sum, it) => sum + it.getPrice(), 0);
      const density = (1 - 1 / mult) / Math.max(cost, 1);
      if (best === null || density > best.density)
        best = { name: me.dname || me.name, bundle, cost, mult, density };
    });
    if (best === null) return order;
    best.bundle.forEach((it) => {
      planned[it.name] = true;
    });
    order.push(best);
  }
}

;// ./src/Cache/Stats/Ascension.js
/** Section: Caches the state of the optimal ascension advisor */








/** Seconds of income history used to average golden cookie effects into the income estimate */
const INCOME_WINDOW = 600;
/** Golden cookies may at most add this multiple of passive income to the estimate */
const MAX_ACTIVE_BONUS = 1;
/** The plan is a dynamic program (~20-60 ms), so it is refreshed less often than once per second */
const PLAN_INTERVAL = 5;
/** Runs younger than this are too short to measure how fast they grow */
const MIN_RUN_TIME = 600;

/**
 * Stores the latest advisor results
 * @item	{object}	state		Inputs of the planner (see PlanAscension)
 * @item	{object}	plan		Result of PlanAscension
 * @item	{boolean}	applicable	False in Born again mode or when no prestige can be earned
 * @item	{object}	heavenlyContext	Income shares valuing heavenly upgrades (see HeavenlyContext)
 * @item	{object[]}	heavenlyOrder	Order in which heavenly chips get spent (see HeavenlyPurchaseOrder)
 */
const AscensionCache = {
  state: null,
  plan: null,
  applicable: false,
  lastPlan: 0,
  heavenlyContext: null,
  heavenlyOrder: [],
};

/**
 * Game.GetHeavenlyMultiplier() with all five "Heavenly ..." store upgrades bought, which every run does
 * within minutes once Legacy is owned
 * @returns	{number}	h in M = 1 + 0.01·h·P
 */
function HeavenlyMultiplierPotential() {
  let mult = 1;
  mult *= 1 + Game.auraMult('Dragon God') * 0.05;
  if (Game.Has('Lucky digit')) mult *= 1.01;
  if (Game.Has('Lucky number')) mult *= 1.01;
  if (Game.Has('Lucky payout')) mult *= 1.01;
  if (Game.hasGod) {
    const godLvl = Game.hasGod('creation');
    if (godLvl === 1) mult *= 0.7;
    else if (godLvl === 2) mult *= 0.8;
    else if (godLvl === 3) mult *= 0.9;
  }
  return mult * Game.heavenlyPower;
}

/**
 * Cookies per second gained from automatic clicking, without click buffs
 * @returns	{number}
 */
function AutoClickIncome() {
  const rate = AutoClickRate();
  if (!rate) return 0;
  let clickBuff = 1;
  Object.keys(Game.buffs).forEach((i) => {
    if (typeof Game.buffs[i].multClick !== 'undefined') clickBuff *= Game.buffs[i].multClick;
  });
  return (rate * Game.computedMouseCps) / (clickBuff > 0 ? clickBuff : 1);
}

/**
 * Collects the inputs of the ascension planner from the game
 * Cookies held by wrinklers and the Chocolate egg payout are counted, as they can be cashed in right
 * before ascending. Income is the unbuffed CpS (with wrinkler returns and automatic clicks), raised to
 * the average income of the last ten minutes once that much history exists, so golden cookies count
 * but a single lucky streak or offline production credited at load cannot dominate the estimate.
 * @returns	{{state: object, heavenly: object, heavenlyContext: object, heavenlyOrder: object[]}}
 */
function GetAscensionInputs() {
  const choEgg =
    Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg') ? CacheLastChoEgg : 0;
  const buffMult = GetCPSBuffMult();
  const clickIncome = AutoClickIncome();
  const baseIncome =
    (Game.cookiesPs * (1 - Game.cpsSucked + CacheCurrWrinklerCPSMult)) /
      (buffMult > 0 ? buffMult : 1) +
    clickIncome;
  let income = baseIncome;
  if (CookiesDiff && WrinkDiff && CookiesDiff.queue.length >= INCOME_WINDOW) {
    const averageIncome =
      CookiesDiff.calcAverage(INCOME_WINDOW) + WrinkDiff.calcAverage(INCOME_WINDOW);
    income = Math.min(Math.max(baseIncome, averageIncome), (1 + MAX_ACTIVE_BONUS) * baseIncome);
  }
  const overhead = Number(
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AscendOverhead,
  );

  const heavenlyContext = HeavenlyContext(baseIncome, clickIncome);
  const heavenlyOrder = HeavenlyPurchaseOrder(heavenlyContext);

  return {
    state: {
      cookiesReset: Game.cookiesReset,
      cookiesRun: Game.cookiesEarned + CacheWrinklersTotal + choEgg,
      income,
      runTime: Math.max(1, (Date.now() - Game.startDate) / 1000),
      overhead: Number.isFinite(overhead) && overhead >= 0 ? overhead : 60,
    },
    heavenly: {
      levels: Game.prestige,
      chips: Game.heavenlyChips,
      hasLegacy: !!Game.Upgrades.Legacy.bought,
      power: HeavenlyMultiplierPotential(),
      // Owned heavenly upgrades speed up the current and future runs alike, so they cancel out
      ownedMult: 1,
      upgrades: heavenlyOrder.map((item) => ({ cost: item.cost, mult: item.mult })),
    },
    heavenlyContext,
    heavenlyOrder,
  };
}

/**
 * This function caches the ascension advisor
 * It is called by CM.Cache.LoopCache() and CM.Cache.InitCache()
 * @param	{boolean}	force	Recalculate now instead of waiting for the next interval
 */
function CacheAscension(force) {
  if (!force && (Game.T / Game.fps) % 1 !== 0) return;

  AscensionCache.applicable = Game.ascensionMode !== 1 && Game.heavenlyPower > 0;
  const now = Date.now() / 1000;
  if (!force && AscensionCache.plan !== null && now - AscensionCache.lastPlan < PLAN_INTERVAL)
    return;
  AscensionCache.lastPlan = now;

  const { state, heavenly, heavenlyContext, heavenlyOrder } = GetAscensionInputs();
  AscensionCache.state = state;
  AscensionCache.heavenlyContext = heavenlyContext;
  AscensionCache.heavenlyOrder = heavenlyOrder;
  AscensionCache.plan =
    state.runTime >= MIN_RUN_TIME
      ? PlanAscension(state, SpeedModel(heavenly))
      : { applicable: false };

  FillCMDCache({
    CacheAscension: {
      applicable: AscensionCache.applicable,
      state: AscensionCache.state,
      plan: AscensionCache.plan,
      heavenlyOrder: heavenlyOrder.map(({ name, cost, mult }) => ({ name, cost, mult })),
    },
  });
}

;// ./src/Disp/HelperFunctions/AscensionSummary.js





/**
 * Formats a percentage with two significant digits for small values
 * @param	{number}	value	Percentage
 * @returns	{string}
 */
function FormatPercent(value) {
  if (!Number.isFinite(value)) return '∞%';
  if (value >= 100) return `${Beautify_Beautify(Math.round(value), 0)}%`;
  if (value === 0) return '0%';
  return `${Number(value.toPrecision(2))}%`;
}

/**
 * Turns the cached advisor plan into the values shown in the stats page, timer bar and ascend tooltip
 * Statuses: 'na' (prestige has no effect), 'early' (run too young to plan), 'none' (no ascension worth
 * a 10% speed-up in sight), 'wait' (keep baking) and 'ready' (ascend now)
 * @returns	{object}	summary
 */
function AscensionSummary() {
  const { applicable, plan, state } = AscensionCache;
  if (!applicable) {
    return {
      status: 'na',
      headline:
        Game.ascensionMode === 1
          ? 'Prestige has no effect in Born again mode'
          : 'Prestige has no effect right now',
      colour: ColourGray,
    };
  }
  if (plan === null || !plan.applicable) {
    return { status: 'early', headline: 'Measuring this run…', colour: ColourGray };
  }

  if (!plan.targetFound) {
    return {
      status: 'none',
      headline: 'Keep baking: no ascension worth it is in sight yet',
      colour: ColourBlue,
      readiness: 0,
      levelsNow: plan.levelsNow,
      speedGainNow: plan.speedGainNow,
      beta: plan.beta,
      runTime: state.runTime,
      shortForecast: '∞',
    };
  }

  const low = Math.min(plan.remainingFast, plan.remainingSlow);
  const high = Math.max(plan.remainingFast, plan.remainingSlow);
  const forecastText =
    ShortDuration(low) === ShortDuration(high)
      ? `≈ ${ShortDuration(plan.remaining)}`
      : `${ShortDuration(low)} – ${ShortDuration(high)}`;

  let status = 'wait';
  let colour = ColourBlue;
  let headline = `Keep baking: optimal ascension in ${forecastText}`;
  if (plan.ascendNow) {
    status = 'ready';
    colour = ColourGreen;
    headline = 'Ascend now: it is the optimal time';
  } else if (plan.readiness >= 0.9) colour = ColourYellow;

  return {
    status,
    headline,
    colour,
    readiness: plan.readiness,
    levelsNow: plan.levelsNow,
    speedGainNow: plan.speedGainNow,
    levelsAtTarget: plan.levelsAtTarget,
    speedGainAtTarget: plan.speedGainAtTarget,
    costOfAscendingNow: plan.costOfAscendingNow,
    forecastText,
    shortForecast: plan.ascendNow ? 'NOW' : ShortDuration(plan.remaining),
    beta: plan.beta,
    runTime: state.runTime,
  };
}

;// ./src/Main/CheckStates/Probability.js
/**
 * The probability that a GC or reindeer has NOT spawned
 */
let chanceTotal = 1.0;
let chanceTotalDeer = 1.0;

/**
 * Clamps a per-frame spawn chance to [0, 1]. Before the game has set a spawn window (minTime equal to
 * maxTime) the chance is NaN, which would otherwise stick in the running product until the next spawn
 * @param {number} chanceToSpawn The probablity that a shimmer appears this frame
 * @returns {number}
 */
function ValidChance(chanceToSpawn) {
  return Number.isNaN(chanceToSpawn) ? 0 : Math.min(Math.max(chanceToSpawn, 0), 1);
}

function resetChanceTotal() {
  chanceTotal = 1.0;
}

function resetChanceTotalDeer() {
  chanceTotalDeer = 1.0;
}

/**
 * Update the probability that a cookie has not spawned
 * @param {number} chanceToSpawn The probablity that a GC appears
 * @returns the cumulative probability that a GC has appeared from beginning to now
 */
function updateChanceTotal(chanceToSpawn) {
  chanceTotal *= 1 - ValidChance(chanceToSpawn);
  return 1 - chanceTotal;
}

/**
 * Update the probability that a reindeer has not spawned
 * @param {number} chanceToSpawn The probablity that a reindeer appears
 * @returns the cumulative probability that a reindeer has appeared from beginning to now
 */
function updateChanceTotalDeer(chanceToSpawn) {
  chanceTotalDeer *= 1 - ValidChance(chanceToSpawn);
  return 1 - chanceTotalDeer;
}

;// ./src/Disp/InfoBars/TimerBar.js
/** Functions related to the Timer Bar */










/**
 * This function creates the TimerBar and appends it to l('wrapper')
 */
function CreateTimerBar() {
  const TimerBar = document.createElement('div');
  TimerBar.id = 'CMTimerBar';
  TimerBar.style.position = 'absolute';
  TimerBar.style.display = 'none';
  TimerBar.style.height = '0px';
  TimerBar.style.fontSize = '10px';
  TimerBar.style.fontWeight = 'bold';
  TimerBar.style.backgroundColor = 'black';

  // Create standard Autosave bar
  const CMTimerBarAutosave = CreateTimer('CMTimerBarAutosave', 'Autosave', [
    { id: 'CMTimerBarAutosaveBar', colour: ColourPurple },
  ]);
  TimerBar.appendChild(CMTimerBarAutosave);

  // Create ascension readiness bar
  const CMTimerBarAscend = CreateTimer('CMTimerBarAscend', 'Ascend', [
    { id: 'CMTimerBarAscendBar', colour: ColourBlue },
  ]);
  TimerBar.appendChild(CMTimerBarAscend);

  // Create autoplay "Lucky!" bank bar, shown while the buyer keeps cookies back for "Lucky!"
  const CMTimerBarLuckyBank = CreateTimer('CMTimerBarLuckyBank', 'Lucky! bank', [
    { id: 'CMTimerBarLuckyBankBar', colour: ColourYellow },
  ]);
  TimerBar.appendChild(CMTimerBarLuckyBank);

  // Create autoplay purchase bar
  const CMTimerBarAutoBuy = CreateTimer('CMTimerBarAutoBuy', 'Next buy', [
    { id: 'CMTimerBarAutoBuyBar', colour: ColourGreen },
  ]);
  TimerBar.appendChild(CMTimerBarAutoBuy);

  // Create standard Golden Cookie bar
  const CMTimerBarGC = CreateTimer('CMTimerBarGC', 'Next Cookie', [
    { id: 'CMTimerBarGCMinBar', colour: ColourGray },
    { id: 'CMTimerBarGCBar', colour: ColourPurple },
  ]);
  TimerBar.appendChild(CMTimerBarGC);

  // Create standard Reindeer bar
  const CMTimerBarRen = CreateTimer('CMTimerBarRen', 'Next Reindeer', [
    { id: 'CMTimerBarRenMinBar', colour: ColourGray },
    { id: 'CMTimerBarRenBar', colour: ColourOrange },
  ]);
  TimerBar.appendChild(CMTimerBarRen);
  const TimerBarBuffTimers = document.createElement('div');
  TimerBarBuffTimers.id = 'CMTimerBarBuffTimers';
  TimerBar.appendChild(TimerBarBuffTimers);

  l('wrapper').appendChild(TimerBar);
}

/**
 * This function updates indivudual timers in the timer bar
 */
function UpdateTimerBar() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1) {
    // label width: 113, timer width: 30, div margin: 20
    const maxWidthTwoBar = l('CMTimerBar').offsetWidth - 163;
    // label width: 113, div margin: 20, calculate timer width at runtime
    const maxWidthOneBar = l('CMTimerBar').offsetWidth - 133;
    let numberOfTimers = 0;

    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutosaveTimerBar &&
      Game.prefs.autosave
    ) {
      const timeTillNextAutosave =
        (Game.fps * 60 - (Game.OnAscend ? 0 : Game.T % (Game.fps * 60))) / Game.fps;
      l('CMTimerBarAutosave').style.display = '';
      l('CMTimerBarAutosaveBar').style.width = `${Math.round(
        (timeTillNextAutosave *
          (maxWidthOneBar - Math.ceil(timeTillNextAutosave).toString().length * 8)) /
          60,
      )}px`;
      if (
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1
      ) {
        l('CMTimerBarAutosaveBar').textContent = Math.ceil(timeTillNextAutosave);
      } else l('CMTimerBarAutosaveBar').textContent = '';
      l('CMTimerBarAutosaveTime').textContent = Math.ceil(timeTillNextAutosave);
      numberOfTimers += 1;
    } else l('CMTimerBarAutosave').style.display = 'none';

    // Ascension readiness: fills up to the optimal ascension time
    const ascension = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings
      .AscendTimerBar
      ? AscensionSummary()
      : null;
    if (ascension !== null && (ascension.status === 'wait' || ascension.status === 'ready')) {
      const label = ascension.shortForecast;
      l('CMTimerBarAscend').style.display = '';
      l('CMTimerBarAscendBar').className = ColourBackPre + ascension.colour;
      l('CMTimerBarAscendBar').style.color = 'black';
      l('CMTimerBarAscendBar').style.width = `${Math.round(
        Math.min(ascension.readiness, 1) * (maxWidthOneBar - label.length * 7 - 8),
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarAscendBar').textContent =
          ascension.readiness >= 0.12
            ? `${Math.floor(Math.min(ascension.readiness, 9.99) * 100)}%`
            : '';
      else l('CMTimerBarAscendBar').textContent = '';
      l('CMTimerBarAscendTime').textContent = label;
      numberOfTimers += 1;
    } else l('CMTimerBarAscend').style.display = 'none';

    // Autoplay: what the buyer is saving for
    const next = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutoBuy
      ? AutoBuyState.next
      : null;

    // The "Lucky!" bank kept back from that purchase, which is why an affordable item can wait
    if (next !== null && next.reason === 'lucky') {
      const banked = Math.min(Game.cookies, next.reserve);
      const label = `${Beautify_Beautify(banked)} / ${Beautify_Beautify(next.reserve)}`;
      l('CMTimerBarLuckyBank').style.display = '';
      l('CMTimerBarLuckyBankBar').style.width = `${Math.round(
        (banked / next.reserve) * Math.max(maxWidthOneBar - label.length * 6 - 8, 0),
      )}px`;
      l('CMTimerBarLuckyBankTime').textContent = label;
      numberOfTimers += 1;
    } else l('CMTimerBarLuckyBank').style.display = 'none';

    if (next !== null) {
      const name = next.name.length > 18 ? `${next.name.slice(0, 17)}…` : next.name;
      const time = next.eta > 0 ? ShortDuration(next.eta) : 'now';
      let label = `${time} ${name}`;
      if (next.reserve > 0 && Game.cookies >= next.price) {
        // Affordable, but the cookies are kept for the "Lucky!" bank or a seasonal action first; in a
        // narrow window the reason matters more than the name
        const why = next.reason === 'season' ? ' (season first)' : ' (Lucky! bank first)';
        label =
          (label.length + why.length) * 6 <= maxWidthOneBar - 8
            ? `${label}${why}`
            : `${time}${why}`;
      }
      l('CMTimerBarAutoBuy').style.display = '';
      l('CMTimerBarAutoBuyBar').style.width = `${Math.round(
        Math.min(Math.max(next.spendable / next.price, 0), 1) *
          Math.max(maxWidthOneBar - label.length * 6 - 8, 0),
      )}px`;
      l('CMTimerBarAutoBuyTime').textContent = label;
      numberOfTimers += 1;
    } else l('CMTimerBarAutoBuy').style.display = 'none';

    // Regulates visibility of Golden Cookie timer
    if (Game.shimmerTypes.golden.spawned === 0 && !Game.Has('Golden switch [off]')) {
      l('CMTimerBarGC').style.display = '';
      l('CMTimerBarGCMinBar').style.width = `${Math.round(
        (Math.max(0, Game.shimmerTypes.golden.minTime - Game.shimmerTypes.golden.time) *
          maxWidthTwoBar) /
          Game.shimmerTypes.golden.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarGCMinBar').textContent = Math.ceil(
          (Game.shimmerTypes.golden.minTime - Game.shimmerTypes.golden.time) / Game.fps,
        );
      else l('CMTimerBarGCMinBar').textContent = '';
      if (Game.shimmerTypes.golden.minTime === Game.shimmerTypes.golden.maxTime) {
        l('CMTimerBarGCMinBar').style.borderTopRightRadius = '10px';
        l('CMTimerBarGCMinBar').style.borderBottomRightRadius = '10px';
      } else {
        l('CMTimerBarGCMinBar').style.borderTopRightRadius = '';
        l('CMTimerBarGCMinBar').style.borderBottomRightRadius = '';
      }
      l('CMTimerBarGCBar').style.width = `${Math.round(
        (Math.min(
          Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.minTime,
          Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.time,
        ) *
          maxWidthTwoBar) /
          Game.shimmerTypes.golden.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarGCBar').textContent = Math.ceil(
          Math.min(
            Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.minTime,
            Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.time,
          ) / Game.fps,
        );
      else l('CMTimerBarGCBar').textContent = '';
      const chanceToSpawn =
        Math.max(
          0,
          (Game.shimmerTypes.golden.time - Game.shimmerTypes.golden.minTime) /
            (Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.minTime),
        ) ** 5;
      const finalChance = updateChanceTotal(chanceToSpawn);
      l('CMTimerBarGCTime').textContent = `${Math.ceil(
        (Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.time) / Game.fps,
      )} `;
      if (finalChance < 0.01) {
        l('CMTimerBarGCTime').textContent +=
          `<${(0.01).toLocaleString('en', { style: 'percent' })}`;
      } else {
        l('CMTimerBarGCTime').textContent += finalChance.toLocaleString('en', {
          style: 'percent',
        });
      }
      numberOfTimers += 1;
    } else l('CMTimerBarGC').style.display = 'none';

    // Regulates visibility of Reindeer timer
    if (Game.season === 'christmas' && Game.shimmerTypes.reindeer.spawned === 0) {
      l('CMTimerBarRen').style.display = '';
      l('CMTimerBarRenMinBar').style.width = `${Math.round(
        (Math.max(0, Game.shimmerTypes.reindeer.minTime - Game.shimmerTypes.reindeer.time) *
          maxWidthTwoBar) /
          Game.shimmerTypes.reindeer.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarRenMinBar').textContent = Math.ceil(
          (Game.shimmerTypes.reindeer.minTime - Game.shimmerTypes.reindeer.time) / Game.fps,
        );
      else l('CMTimerBarRenMinBar').textContent = '';
      l('CMTimerBarRenBar').style.width = `${Math.round(
        (Math.min(
          Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.minTime,
          Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.time,
        ) *
          maxWidthTwoBar) /
          Game.shimmerTypes.reindeer.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarRenBar').textContent = Math.ceil(
          Math.min(
            Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.minTime,
            Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.time,
          ) / Game.fps,
        );
      else l('CMTimerBarRenBar').textContent = '';
      const chanceToSpawn =
        Math.max(
          0,
          (Game.shimmerTypes.reindeer.time - Game.shimmerTypes.reindeer.minTime) /
            (Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.minTime),
        ) ** 5;
      const deerFinalChance = updateChanceTotalDeer(chanceToSpawn);
      l('CMTimerBarRenTime').textContent = `${Math.ceil(
        (Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.time) / Game.fps,
      )} `;
      if (deerFinalChance < 0.01) {
        l('CMTimerBarRenTime').textContent +=
          `<${(0.01).toLocaleString('en', { style: 'percent' })}`;
      } else {
        l('CMTimerBarRenTime').textContent += deerFinalChance.toLocaleString('en', {
          style: 'percent',
        });
      }
      numberOfTimers += 1;
    } else {
      l('CMTimerBarRen').style.display = 'none';
    }

    // On every frame all buff-timers are deleted and re-created
    const BuffTimerBars = {};
    l('CMTimerBarBuffTimers').innerHTML = '';
    Object.keys(Game.buffs).forEach((i) => {
      if (Game.buffs[i]) {
        const timer = CreateTimer(Game.buffs[i].name, Game.buffs[i].name, [
          { id: `${Game.buffs[i].name}Bar` },
        ]);
        timer.style.display = '';
        let classColour = '';
        // Gives specific timers specific colours
        if (typeof BuffColours[Game.buffs[i].name] !== 'undefined') {
          classColour = BuffColours[Game.buffs[i].name];
        } else classColour = ColourPurple;
        timer.lastChild.children[1].className = ColourBackPre + classColour;
        timer.lastChild.children[1].style.color = 'black';
        if (
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay === 2
        )
          timer.lastChild.children[1].textContent = `${Math.round(
            100 * (Game.buffs[i].time / Game.buffs[i].maxTime),
          )}%`;
        else timer.lastChild.children[1].textContent = '';
        timer.lastChild.children[1].style.width = `${Math.round(
          (Game.buffs[i].time *
            (maxWidthOneBar - Math.ceil(Game.buffs[i].time / Game.fps).toString().length * 8)) /
            Game.buffs[i].maxTime,
        )}px`;
        timer.lastChild.children[2].textContent = Math.ceil(Game.buffs[i].time / Game.fps);
        numberOfTimers += 1;
        BuffTimerBars[Game.buffs[i].name] = timer;
      }
    });
    Object.keys(BuffTimerBars).forEach((i) => {
      l('CMTimerBarBuffTimers').appendChild(BuffTimerBars[i]);
    });

    if (numberOfTimers !== 0) {
      l('CMTimerBar').style.height = `${numberOfTimers * 12 + 2}px`;
    }
    if (LastNumberOfTimers !== numberOfTimers) {
      LastNumberOfTimers = numberOfTimers;
      UpdateBotTimerBarPosition();
    }
  }
}

;// ./src/Disp/MenuSections/Refreshmenu.js
/**
 * This function refreshes the stats page, CM.Options.UpStats determines the rate at which that happens
 * It is called by CM.Disp.Draw()
 */
function RefreshMenu() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.UpStats &&
    Game.onMenu === 'stats' &&
    (Game.drawT - 1) % (Game.fps * 5) !== 0 &&
    (Game.drawT - 1) % Game.fps === 0
  )
    Game.UpdateMenu();
}

;// ./src/Cache/Dragon/CacheDragonAuras.js
 // eslint-disable-line no-unused-vars

/**
 * This functions caches the currently selected Dragon Auras
 */
function CacheDragonAuras() {
  CacheDragonAura = Game.dragonAura;
  CacheDragonAura2 = Game.dragonAura2;
}

;// ./src/Sim/InitializeData/InitAchievement.js
/**
 * This function constructs an object with the static properties of an achievement
 * @param	{string}	achievementName	Name of the Achievement
 * @returns {Object}	you				The static object
 */
function InitAchievement(achievementName) {
  const me = Game.Achievements[achievementName];
  const you = {};
  you.name = me.name;
  return you;
}

;// ./src/Sim/ReplacedGameFunctions/SimGetTieredCpsMult.js



/**
 * This functions creates functions similarly to Game.GetTieredCpsMult but checks Sim Data instead of Game Data
 */
function SimGetTieredCpsMult(me) {
  let mult = 1;
  Object.keys(me.tieredUpgrades).forEach((i) => {
    if (!Game.Tiers[me.tieredUpgrades[i].tier].special && SimHas(me.tieredUpgrades[i].name)) {
      let tierMult = 2;
      // unshackled multipliers
      if (
        Game.ascensionMode !== 1 &&
        SimHas(me.unshackleUpgrade) &&
        SimHas(Game.Tiers[me.tieredUpgrades[i].tier].unshackleUpgrade)
      )
        tierMult += me.id === 1 ? 0.5 : (20 - me.id) * 0.1;
      mult *= tierMult;
    }
  });
  Object.keys(me.synergies).forEach((i) => {
    if (SimHas(me.synergies[i].name)) {
      const syn = me.synergies[i];
      if (syn.buildingTie1.name === me.name) mult *= 1 + 0.05 * syn.buildingTie2.amount;
      else if (syn.buildingTie2.name === me.name) mult *= 1 + 0.001 * syn.buildingTie1.amount;
    }
  });
  if (me.fortune && SimHas(me.fortune.name)) mult *= 1.07;
  if (me.grandma && SimHas(me.grandma.name))
    mult *= 1 + SimObjects.Grandma.amount * 0.01 * (1 / (me.id - 1));
  if (typeof me.tieredUpgrades.misfortune === 'object') {
    if (me.vanilla === 1 && SimHas(me.tieredUpgrades.misfortune.name)) {
      switch (Game.elderWrath) {
        case 1:
          mult *= 1.02;
          break;
        case 2:
          mult *= 1.04;
          break;
        case 3:
          mult *= 1.06;
          break;
        default:
          mult *= 1;
          break;
      }
    }
  }
  return mult;
}

;// ./src/Sim/InitializeData/InitialBuildingData.js






/**
 * This function constructs an object with the static properties of a building,
 * but with a 'cps' method changed to check sim data
 *
 * @param	{string}	buildingName	Name of the building
 * @returns {Object}	you				The static object
 */
function InitialBuildingData(buildingName) {
  const me = Game.Objects[buildingName];
  const you = {};
  if (me.name === 'Cursor') {
    you.cps = function (it) {
      let add = 0;
      if (SimHas('Thousand fingers')) add += 0.1;
      if (SimHas('Million fingers')) add *= 5;
      if (SimHas('Billion fingers')) add *= 10;
      if (SimHas('Trillion fingers')) add *= 20;
      if (SimHas('Quadrillion fingers')) add *= 20;
      if (SimHas('Quintillion fingers')) add *= 20;
      if (SimHas('Sextillion fingers')) add *= 20;
      if (SimHas('Septillion fingers')) add *= 20;
      if (SimHas('Octillion fingers')) add *= 20;
      if (SimHas('Nonillion fingers')) add *= 20;
      if (SimHas('Decillion fingers')) add *= 20;
      if (SimHas('Undecillion fingers')) add *= 20;
      if (SimHas('Unshackled cursors')) add *= 25;
      let mult = 1;
      let num = 0;
      Object.keys(SimObjects).forEach((i) => {
        if (SimObjects[i].name !== 'Cursor') num += SimObjects[i].amount;
      });
      add *= num;
      mult *= SimGetTieredCpsMult(it);
      mult *= Game.magicCpS('Cursor');
      mult *= SimEff('cursorCps');
      return (
        Game.ComputeCps(
          0.1,
          SimHas('Reinforced index finger') +
            SimHas('Carpal tunnel prevention cream') +
            SimHas('Ambidextrous'),
          add,
        ) * mult
      );
    };
  } else if (me.name === 'Grandma') {
    you.cps = function (it) {
      let mult = 1;
      Object.keys(Game.GrandmaSynergies).forEach((i) => {
        if (SimHas(Game.GrandmaSynergies[i])) mult *= 2;
      });
      if (SimHas('Bingo center/Research facility')) mult *= 4;
      if (SimHas('Ritual rolling pins')) mult *= 2;
      if (SimHas('Naughty list')) mult *= 2;

      if (SimHas('Elderwort biscuits')) mult *= 1.02;

      mult *= SimEff('grandmaCps');

      if (SimHas('Cat ladies')) {
        for (let i = 0; i < Game.UpgradesByPool.kitten.length; i++) {
          if (SimHas(Game.UpgradesByPool.kitten[i].name)) mult *= 1.29;
        }
      }

      mult *= SimGetTieredCpsMult(it);

      let add = 0;
      if (SimHas('One mind')) add += SimObjects.Grandma.amount * 0.02;
      if (SimHas('Communal brainsweep')) add += SimObjects.Grandma.amount * 0.02;
      if (SimHas('Elder Pact')) add += SimObjects.Portal.amount * 0.05;

      let num = 0;
      Object.keys(SimObjects).forEach((i) => {
        if (SimObjects[i].name !== 'Grandma') num += SimObjects[i].amount;
      });
      // if (Game.hasAura('Elder Battalion')) mult*=1+0.01*num;
      mult *= 1 + SimAuraMult('Elder Battalion') * 0.01 * num;

      mult *= Game.magicCpS(me.name);

      return (me.baseCps + add) * mult;
    };
  } else {
    you.cps = function (it) {
      let mult = 1;
      mult *= SimGetTieredCpsMult(it);
      mult *= Game.magicCpS(it.name);
      return it.baseCPS * mult;
    };
  }

  // Below is needed for above eval, specifically for the SimGetTieredCpsMult function
  you.baseCps = me.baseCps;
  you.name = me.name;
  you.tieredUpgrades = me.tieredUpgrades;
  you.synergies = me.synergies;
  you.fortune = me.fortune;
  you.grandma = me.grandma;
  you.baseCPS = me.baseCps;
  you.id = me.id;
  you.vanilla = me.vanilla;
  you.unshackleUpgrade = me.unshackleUpgrade;
  return you;
}

;// ./src/Sim/InitializeData/InitUpgrade.js




/**
 * This function constructs an object with the static properties of an upgrade
 * @param	{string}	upgradeName		Name of the Upgrade
 * @returns {Object}	you				The static object
 */
function InitUpgrade(upgradeName) {
  const me = Game.Upgrades[upgradeName];
  const you = {};
  // Some upgrades have a function for .power (notably the valentine cookies)
  you.power = me.power;
  if (typeof you.power === 'function') {
    if (me.name === 'Sugar crystal cookies') {
      you.power = function () {
        let n = 5;
        Object.keys(SimObjects).forEach((i) => {
          if (SimObjects[i].level >= 10) n += 1;
        });
        return n;
      };
    } else {
      you.power = function () {
        let pow = 2;
        if (SimHas('Starlove')) pow = 3;
        if (Game.hasGod) {
          const godLvl = SimHasGod('seasons');
          if (godLvl === 1) pow *= 1.3;
          else if (godLvl === 2) pow *= 1.2;
          else if (godLvl === 3) pow *= 1.1;
        }
        return pow;
      };
    }
  }
  you.pool = me.pool;
  you.name = me.name;
  return you;
}

;// ./src/Sim/SimulationData/CopyData.js








/**
 * This function copies all relevant data and therefore sets a new iteration of the "sim data"
 * It is called at the start of any function that simulates certain behaviour or actions
 */
function CopyData() {
  // Other variables
  SimUpgradesOwned = Game.UpgradesOwned;
  SimPledges = Game.pledges;
  SimAchievementsOwned = Game.AchievementsOwned;
  SimHeavenlyPower = Game.heavenlyPower;
  SimPrestige = Game.prestige;

  // Buildings
  Object.keys(Game.Objects).forEach((i) => {
    const me = Game.Objects[i];
    let you = SimObjects[i];
    if (you === undefined) {
      // New building!
      SimObjects[i] = InitialBuildingData(i);
      you = SimObjects[i];
      CreateBotBarBuildingColumn(i); // Add new building to the bottom bar
    }
    you.amount = me.amount;
    you.level = me.level;
    you.totalCookies = me.totalCookies;
    you.basePrice = me.basePrice;
    you.free = me.free;
    if (me.minigameLoaded) {
      if (me.name === 'Temple') {
        SimGod1 = me.minigame.slot[0];
        SimGod2 = me.minigame.slot[1];
        SimGod3 = me.minigame.slot[2];
      }
      you.minigameLoaded = me.minigameLoaded;
      you.minigame = me.minigame;
    }
    SimObjects[i] = you;
  });

  // Upgrades
  Object.keys(Game.Upgrades).forEach((i) => {
    const me = Game.Upgrades[i];
    let you = SimUpgrades[i];
    if (you === undefined) {
      SimUpgrades[i] = InitUpgrade(i);
      you = SimUpgrades[i];
    }
    you.bought = me.bought;
    SimUpgrades[i] = you;
  });

  // Achievements
  Object.keys(Game.Achievements).forEach((i) => {
    const me = Game.Achievements[i];
    let you = SimAchievements[i];
    if (you === undefined) {
      SimAchievements[i] = InitAchievement(i);
      you = SimAchievements[i];
    }
    you.won = me.won;
    SimAchievements[i] = you;
  });

  // Auras
  CacheDragonAuras();
  SimDragonAura = CacheDragonAura;
  SimDragonAura2 = CacheDragonAura2;
}

;// ./src/Disp/Tooltips/CreateTooltip.js


/** Creates various sections of tooltips */

/**
 * This function creates a tooltipBox object which contains all CookieMonster added tooltip information.
 * @returns {object}	div		An object containing the stylized box
 */
function TooltipCreateTooltipBox() {
  l('tooltip').firstChild.style.paddingBottom = '4px'; // Sets padding on base-tooltip
  const tooltipBox = document.createElement('div');
  tooltipBox.style.border = '1px solid';
  tooltipBox.style.padding = '4px';
  tooltipBox.style.margin = '0px -4px';
  tooltipBox.id = 'CMTooltipBorder';
  tooltipBox.className = ColourTextPre + ColourGray;
  return tooltipBox;
}

/**
 * This function creates a header object for tooltips.
 * @param	{string}	text	Title of header, also used for its id
 * @param	{string}	[label]	Text to display instead of the title
 * @returns {object}	div		An object containing the stylized header
 */
function TooltipCreateHeader(text, label) {
  const div = document.createElement('div');
  div.style.fontWeight = 'bold';
  div.id = `${text}Title`;
  div.className = ColourTextPre + ColourBlue;
  div.textContent = typeof label === 'undefined' ? text : label;
  return div;
}

/**
 * This function creates the tooltip object for warnings: one box with a row per bank threshold
 * The object is also removed by CM.Disp.UpdateTooltipWarnings() when type is 's' or 'g'
 * @returns {object}	TooltipWarn	The Warnings-tooltip object
 */
function TooltipCreateWarningSection() {
  const TooltipWarn = document.createElement('div');
  TooltipWarn.style.position = 'absolute';
  TooltipWarn.style.display = 'block';
  TooltipWarn.style.left = 'auto';
  TooltipWarn.style.bottom = 'auto';
  TooltipWarn.id = 'CMDispTooltipWarningParent';

  const box = document.createElement('div');
  box.id = 'CMDispTooltipWarnBox';
  box.className = `CMWarnBox ${ColourBorderPre}${ColourRed}`;
  box.style.display = 'none';
  const title = document.createElement('div');
  title.className = `CMWarnTitle ${ColourTextPre}${ColourRed}`;
  title.textContent = 'Buying this drops your bank below:';
  box.appendChild(title);

  const create = function (rowId, colour, label, deficitId, tooltip) {
    const row = document.createElement('div');
    row.id = rowId;
    row.className = 'CMWarnRow';
    row.style.display = 'none';
    row.title = tooltip;
    const labelSpan = document.createElement('span');
    labelSpan.className = ColourTextPre + colour;
    labelSpan.textContent = label;
    row.appendChild(labelSpan);
    const deficitSpan = document.createElement('span');
    deficitSpan.id = deficitId;
    row.appendChild(deficitSpan);
    return row;
  };

  box.appendChild(
    create(
      'CMDispTooltipWarnLucky',
      ColourRed,
      '"Lucky!"',
      'CMDispTooltipWarnLuckyText',
      'Bank needed for a maximum "Lucky!" reward',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnLuckyFrenzy',
      ColourYellow,
      '"Lucky!" (Frenzy)',
      'CMDispTooltipWarnLuckyFrenzyText',
      'Bank needed for a maximum "Lucky!" reward during a Frenzy',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnConjure',
      ColourPurple,
      'Conjure Baked Goods',
      'CMDispTooltipWarnConjureText',
      'Bank needed for a maximum "Conjure Baked Goods" reward',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnConjureFrenzy',
      ColourPurple,
      'Conjure (Frenzy)',
      'CMDispTooltipWarnConjureFrenzyText',
      'Bank needed for a maximum "Conjure Baked Goods" reward during a Frenzy',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnEdifice',
      ColourPurple,
      'Spontaneous Edifice',
      'CMDispTooltipWarnEdificeText',
      'Bank needed for "Spontaneous Edifice" to possibly give you your most expensive building',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnUser',
      ColourRed,
      `${Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnUser}s of CPS`,
      'CMDispTooltipWarnUserText',
      'Custom warning set in the Cookie Monster settings',
    ),
  );
  TooltipWarn.appendChild(box);

  return TooltipWarn;
}

/**
 * This function appends the sections for Bonus Income, PP and Time left (to achiev) to the tooltip-object
 * They are laid out as a two-column grid of label and value; the actual data is added by the Update-functions
 * @param	{object}	tooltip		Object of a TooltipBox, normally created by a call to CM.Disp.TooltipCreateTooltipBox()
 */
function TooltipCreateCalculationSection(tooltip) {
  const grid = document.createElement('div');
  grid.className = 'CMTooltipGrid';
  grid.id = 'CMTooltipGrid';
  const add = function (title, label, valueId, hidden) {
    const header = TooltipCreateHeader(title, label);
    header.classList.add('CMTooltipLabel');
    const value = document.createElement('div');
    value.id = valueId;
    value.className = 'CMTooltipValue';
    if (hidden) {
      header.style.display = 'none';
      value.style.display = 'none';
    }
    grid.appendChild(header);
    grid.appendChild(value);
    return header;
  };

  add('Bonus Income', 'Bonus income', 'CMTooltipIncome');
  add('Bonus Cookies per Click', 'Bonus per click', 'CMTooltipCookiePerClick', true);
  add('Payback Period', 'Payback period', 'CMTooltipPP');
  add('Time Left', 'Time left', 'CMTooltipTime');
  if (TooltipType === 'b') {
    add(
      'Production left till next achievement',
      'Output achiev. in',
      'CMTooltipProductionLeft',
      true,
    ).id = 'CMTooltipProductionLeftHeader';
    add(
      'Buildings (price / PP) left till next achievement',
      'Count achiev. in',
      'CMTooltipNextAchievement',
      true,
    ).id = 'CMTooltipNextAchievementHeader';
  }
  tooltip.appendChild(grid);
}

;// ./src/Cache/PP/ColourOfPP.js




/**
 * This functions return the colour assosciated with the given pp value
 * It is called by CM.Cache.CacheBuildingsPP(), CM.Cache.CacheBuildingsBulkPP() and CM.Cache.CacheUpgradePP()
 * @params	{object}	obj		The obj of which the pp value should be checked
 * @params	{number}	price	The price of the object
 * @returns {string}	colour	The colour assosciated with the pp value
 */
function ColourOfPP(me, price) {
  let colour = '';
  // Colour based on PP
  if (me.pp <= 0 || me.pp === Infinity) colour = ColourGray;
  else if (me.pp < CacheMinPP) colour = ColourBlue;
  else if (me.pp === CacheMinPP) colour = ColourGreen;
  else if (me.pp < CachePPArray[10][0]) colour = ColourYellow;
  else if (me.pp < CachePPArray[20][0]) colour = ColourOrange;
  else if (me.pp < CachePPArray[30][0]) colour = ColourRed;
  else colour = ColourPurple;

  // Colour based on price in terms of CPS
  if (
    Number(
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPSecondsLowerLimit,
    ) !== 0
  ) {
    if (
      price / GetCPS() <
      Number(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPSecondsLowerLimit,
      )
    )
      colour = ColourBlue;
  }
  // Colour based on being able to purchase
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPOnlyConsiderBuyable) {
    if (price - Game.cookies > 0) colour = ColourRed;
  }
  return colour;
}

;// ./src/Sim/ReplacedGameFunctions/SimGetHeavenlyMultiplier.js




/**
 * This functions creates functions similarly to Game.GetHeavenlyMultiplier but checks Sim Data instead of Game Data
 */
function SimGetHeavenlyMultiplier() {
  let heavenlyMult = 0;
  if (SimHas('Heavenly chip secret')) heavenlyMult += 0.05;
  if (SimHas('Heavenly cookie stand')) heavenlyMult += 0.2;
  if (SimHas('Heavenly bakery')) heavenlyMult += 0.25;
  if (SimHas('Heavenly confectionery')) heavenlyMult += 0.25;
  if (SimHas('Heavenly key')) heavenlyMult += 0.25;
  // if (SimHasAura('Dragon God')) heavenlyMult*=1.05;
  heavenlyMult *= 1 + SimAuraMult('Dragon God') * 0.05;
  if (SimHas('Lucky digit')) heavenlyMult *= 1.01;
  if (SimHas('Lucky number')) heavenlyMult *= 1.01;
  if (SimHas('Lucky payout')) heavenlyMult *= 1.01;
  if (Game.hasGod) {
    const godLvl = SimHasGod('creation');
    if (godLvl === 1) heavenlyMult *= 0.7;
    else if (godLvl === 2) heavenlyMult *= 0.8;
    else if (godLvl === 3) heavenlyMult *= 0.9;
  }
  return heavenlyMult;
}

;// ./src/Sim/SimulationData/SimWin.js
 // eslint-disable-line no-unused-vars

/**
 * This function "wins" an achievement in the current sim data
 * It functions similarly to Game.Win()
 * It is not created by CM.Sim.CreateSimFunctions() in order to avoid spamming pop-ups upon winning
 * @param	{string}	what	Name of the achievement
 */
function SimWin(what) {
  if (SimAchievements[what]) {
    if (SimAchievements[what].won === 0) {
      SimAchievements[what].won = 1;
      if (Game.Achievements[what].pool !== 'shadow') SimAchievementsOwned += 1;
    }
  }
}

;// ./src/Sim/Calculations/CalculateGains.js











/**
 * This function calculates the CPS of the current "sim data"
 * It is similar to Game.CalculateGains()
 * It is called at the start of any function that simulates certain behaviour or actions
 * @global	{number}	CM.Sim.cookiesPs	The CPS of the current sim data
 */
function CalculateGains() {
  SimCookiesPs = 0;
  let mult = 1;
  // Include minigame effects
  const effs = {};
  Object.keys(Game.Objects).forEach((i) => {
    if (Game.Objects[i].minigameLoaded && Game.Objects[i].minigame.effs) {
      const myEffs = Game.Objects[i].minigame.effs;
      Object.keys(myEffs).forEach((ii) => {
        if (effs[ii]) effs[ii] *= myEffs[ii];
        else effs[ii] = myEffs[ii];
      });
    }
  });
  SimEffs = effs;

  if (Game.ascensionMode !== 1)
    mult += parseFloat(SimPrestige) * 0.01 * SimHeavenlyPower * SimGetHeavenlyMultiplier();

  mult *= SimEff('cps');

  if (SimHas('Heralds') && Game.ascensionMode !== 1) mult *= 1 + 0.01 * Game.heralds;

  Object.keys(Game.cookieUpgrades).forEach((i) => {
    const me = Game.cookieUpgrades[i];
    if (SimHas(me.name)) {
      // Some upgrades have a function as .power (notably the valentine cookies)
      // CM.Sim.InitialBuildingData has changed to use CM.Sim.Has instead of Game.Has etc.
      // Therefore this call is to the .power of the Sim.Object
      if (typeof me.power === 'function') {
        mult *= 1 + SimUpgrades[me.name].power(SimUpgrades[me.name]) * 0.01;
      } else mult *= 1 + me.power * 0.01;
    }
  });

  if (SimHas('Specialized chocolate chips')) mult *= 1.01;
  if (SimHas('Designer cocoa beans')) mult *= 1.02;
  if (SimHas('Underworld ovens')) mult *= 1.03;
  if (SimHas('Exotic nuts')) mult *= 1.04;
  if (SimHas('Arcane sugar')) mult *= 1.05;

  if (SimHas('Increased merriness')) mult *= 1.15;
  if (SimHas('Improved jolliness')) mult *= 1.15;
  if (SimHas('A lump of coal')) mult *= 1.01;
  if (SimHas('An itchy sweater')) mult *= 1.01;
  if (SimHas("Santa's dominion")) mult *= 1.2;

  if (SimHas('Fortune #100')) mult *= 1.01;
  if (SimHas('Fortune #101')) mult *= 1.07;

  if (SimHas('Dragon scale')) mult *= 1.03;

  if (SimHas('Wrinkler ambergris')) mult *= 1.06;

  // Check effect of chosen Gods
  let buildMult = 1;
  if (SimHasGod) {
    let godLvl = SimHasGod('asceticism');
    if (godLvl === 1) mult *= 1.15;
    else if (godLvl === 2) mult *= 1.1;
    else if (godLvl === 3) mult *= 1.05;

    godLvl = SimHasGod('ages');
    if (godLvl === 1)
      mult *= 1 + 0.15 * Math.sin((CycliusDateAtBeginLoop / 1000 / (60 * 60 * 3)) * Math.PI * 2);
    else if (godLvl === 2)
      mult *= 1 + 0.15 * Math.sin((CycliusDateAtBeginLoop / 1000 / (60 * 60 * 12)) * Math.PI * 2);
    else if (godLvl === 3)
      mult *= 1 + 0.15 * Math.sin((CycliusDateAtBeginLoop / 1000 / (60 * 60 * 24)) * Math.PI * 2);

    godLvl = SimHasGod('decadence');
    if (godLvl === 1) buildMult *= 0.93;
    else if (godLvl === 2) buildMult *= 0.95;
    else if (godLvl === 3) buildMult *= 0.98;

    godLvl = SimHasGod('industry');
    if (godLvl === 1) buildMult *= 1.1;
    else if (godLvl === 2) buildMult *= 1.06;
    else if (godLvl === 3) buildMult *= 1.03;

    godLvl = SimHasGod('labor');
    if (godLvl === 1) buildMult *= 0.97;
    else if (godLvl === 2) buildMult *= 0.98;
    else if (godLvl === 3) buildMult *= 0.99;
  }

  if (SimHas("Santa's legacy")) mult *= 1 + (Game.santaLevel + 1) * 0.03;

  const milkProgress = SimAchievementsOwned / 25;
  let milkMult = 1;
  if (SimHas("Santa's milk and cookies")) milkMult *= 1.05;
  // if (CM.Sim.hasAura('Breath of Milk')) milkMult *= 1.05;
  milkMult *= 1 + SimAuraMult('Breath of Milk') * 0.05;
  if (SimHasGod) {
    const godLvl = SimHasGod('mother');
    if (godLvl === 1) milkMult *= 1.1;
    else if (godLvl === 2) milkMult *= 1.05;
    else if (godLvl === 3) milkMult *= 1.03;
  }
  milkMult *= SimEff('milk');

  let catMult = 1;

  if (SimHas('Kitten helpers')) catMult *= 1 + milkProgress * 0.1 * milkMult;
  if (SimHas('Kitten workers')) catMult *= 1 + milkProgress * 0.125 * milkMult;
  if (SimHas('Kitten engineers')) catMult *= 1 + milkProgress * 0.15 * milkMult;
  if (SimHas('Kitten overseers')) catMult *= 1 + milkProgress * 0.175 * milkMult;
  if (SimHas('Kitten managers')) catMult *= 1 + milkProgress * 0.2 * milkMult;
  if (SimHas('Kitten accountants')) catMult *= 1 + milkProgress * 0.2 * milkMult;
  if (SimHas('Kitten specialists')) catMult *= 1 + milkProgress * 0.2 * milkMult;
  if (SimHas('Kitten experts')) catMult *= 1 + milkProgress * 0.2 * milkMult;
  if (SimHas('Kitten consultants')) catMult *= 1 + milkProgress * 0.2 * milkMult;
  if (SimHas('Kitten assistants to the regional manager'))
    catMult *= 1 + milkProgress * 0.175 * milkMult;
  if (SimHas('Kitten marketeers')) catMult *= 1 + milkProgress * 0.15 * milkMult;
  if (SimHas('Kitten analysts')) catMult *= 1 + milkProgress * 0.125 * milkMult;
  if (SimHas('Kitten executives')) catMult *= 1 + milkProgress * 0.115 * milkMult;
  if (SimHas('Kitten admins')) catMult *= 1 + milkProgress * 0.11 * milkMult;
  if (SimHas('Kitten strategists')) catMult *= 1 + milkProgress * 0.105 * milkMult;
  if (SimHas('Kitten angels')) catMult *= 1 + milkProgress * 0.1 * milkMult;
  if (SimHas('Fortune #103')) catMult *= 1 + milkProgress * 0.05 * milkMult;

  Object.keys(SimObjects).forEach((i) => {
    const me = SimObjects[i];
    let storedCps = me.cps(me);
    if (Game.ascensionMode !== 1) storedCps *= (1 + me.level * 0.01) * buildMult;
    if (me.name === 'Grandma' && SimHas('Milkhelp&reg; lactose intolerance relief tablets'))
      storedCps *= 1 + 0.05 * milkProgress * milkMult;
    SimCookiesPs += me.amount * storedCps;
  });

  if (SimHas('"egg"')) SimCookiesPs += 9; // "egg"

  mult *= catMult;

  let eggMult = 1;
  if (SimHas('Chicken egg')) eggMult *= 1.01;
  if (SimHas('Duck egg')) eggMult *= 1.01;
  if (SimHas('Turkey egg')) eggMult *= 1.01;
  if (SimHas('Quail egg')) eggMult *= 1.01;
  if (SimHas('Robin egg')) eggMult *= 1.01;
  if (SimHas('Ostrich egg')) eggMult *= 1.01;
  if (SimHas('Cassowary egg')) eggMult *= 1.01;
  if (SimHas('Salmon roe')) eggMult *= 1.01;
  if (SimHas('Frogspawn')) eggMult *= 1.01;
  if (SimHas('Shark egg')) eggMult *= 1.01;
  if (SimHas('Turtle egg')) eggMult *= 1.01;
  if (SimHas('Ant larva')) eggMult *= 1.01;
  if (SimHas('Century egg')) {
    // The boost increases a little every day, with diminishing returns up to +10% on the 100th day
    let day =
      (Math.floor((CenturyDateAtBeginLoop - Game.startDate) / 1000 / 10) * 10) / 60 / 60 / 24;
    day = Math.min(day, 100);
    // Sets a Cache value to be displayed in the Stats page, could be moved...
    CacheCentEgg = 1 + (1 - (1 - day / 100) ** 3) * 0.1;
    eggMult *= CacheCentEgg;
  }
  mult *= eggMult;

  if (SimHas('Sugar baking')) mult *= 1 + Math.min(100, Game.lumps) * 0.01;

  // if (CM.Sim.hasAura('Radiant Appetite')) mult *= 2;
  mult *= 1 + SimAuraMult('Radiant Appetite');

  const rawCookiesPs = SimCookiesPs * mult;
  Object.keys(Game.CpsAchievements).forEach((i) => {
    if (rawCookiesPs >= Game.CpsAchievements[i].threshold) SimWin(Game.CpsAchievements[i].name);
  });

  SimCookiesPsRaw = rawCookiesPs;

  const { n } = Game.shimmerTypes.golden;
  const auraMult = SimAuraMult("Dragon's Fortune");
  for (let i = 0; i < n; i++) {
    mult *= 1 + auraMult * 1.23;
  }

  const name = Game.bakeryName.toLowerCase();
  if (name === 'orteil') mult *= 0.99;
  else if (name === 'ortiel') mult *= 0.98;

  if (SimHas('Elder Covenant')) mult *= 0.95;

  if (SimHas('Golden switch [off]')) {
    let goldenSwitchMult = 1.5;
    if (SimHas('Residual luck')) {
      const upgrades = Game.goldenCookieUpgrades;
      Object.keys(upgrades).forEach((i) => {
        if (SimHas(upgrades[i])) goldenSwitchMult += 0.1;
      });
    }
    mult *= goldenSwitchMult;
  }
  if (SimHas('Shimmering veil [off]')) {
    let veilMult = 0.5;
    if (SimHas('Reinforced membrane')) veilMult += 0.1;
    if (SimHas('Delicate touch')) veilMult += 0.05;
    if (SimHas('Steadfast murmur')) veilMult += 0.05;
    if (SimHas('Glittering edge')) veilMult += 0.05;
    mult *= 1 + veilMult;
  }

  if (SimHas('Magic shenanigans')) mult *= 1000;
  if (SimHas('Occult obstruction')) mult *= 0;

  SimCookiesPs = Game.runModHookOnValue('cps', SimCookiesPs);

  mult *= GetCPSBuffMult();

  SimCookiesPs *= mult;

  // if (Game.hasBuff('Cursed finger')) Game.cookiesPs = 0;
}

;// ./src/Data/Gamedata.js
/** Data copied directly from the game */

/** Array of the names of all fortune cookies obtainable from the ticker */
const Fortunes = [
  'Fortune #001',
  'Fortune #002',
  'Fortune #003',
  'Fortune #004',
  'Fortune #005',
  'Fortune #006',
  'Fortune #007',
  'Fortune #008',
  'Fortune #009',
  'Fortune #010',
  'Fortune #011',
  'Fortune #012',
  'Fortune #013',
  'Fortune #014',
  'Fortune #015',
  'Fortune #016',
  'Fortune #017',
  'Fortune #018',
  'Fortune #019',
  'Fortune #020',
  'Fortune #100',
  'Fortune #101',
  'Fortune #102',
  'Fortune #103',
  'Fortune #104',
];

/** Array of the names of all Halloween cookies */
const HalloCookies = [
  'Skull cookies',
  'Ghost cookies',
  'Bat cookies',
  'Slime cookies',
  'Pumpkin cookies',
  'Eyeball cookies',
  'Spider cookies',
];

/** Array of the names of all Christmas cookies */
const ChristCookies = [
  'Christmas tree biscuits',
  'Snowflake biscuits',
  'Snowman biscuits',
  'Holly biscuits',
  'Candy cane biscuits',
  'Bell biscuits',
  'Present biscuits',
];

/** Array of the names of all Valentine cookies */
const ValCookies = [
  'Pure heart biscuits',
  'Ardent heart biscuits',
  'Sour heart biscuits',
  'Weeping heart biscuits',
  'Golden heart biscuits',
  'Eternal heart biscuits',
  'Prism heart biscuits',
];

/** Array of the names of all plant drops */
const PlantDrops = [
  'Elderwort biscuits',
  'Bakeberry cookies',
  'Duketater cookies',
  'Green yeast digestives',
  'Wheat slims',
  'Fern tea',
  'Ichor syrup',
];

/** All possible effects plants and other items can have with a display-title */
const Effects = {
  buildingCost: 'Building prices',
  click: 'Cookies per click',
  cps: 'Total CPS',
  cursorCps: 'Cursor CPS',
  goldenCookieDur: 'Golden cookie duration',
  goldenCookieEffDur: 'Golden cookie effect duration',
  goldenCookieFreq: 'Golden cookie frequency',
  goldenCookieGain: 'Golden cookie gains',
  grandmaCps: 'Grandma CPS',
  itemDrops: 'Random item drop chance',
  milk: 'Effect from milk',
  reindeerDur: 'Reindeer duration',
  reindeerFreq: 'Reindeer frequency',
  reindeerGain: 'Reindeer gains',
  upgradeCost: 'Upgrade prices',
  wrathCookieDur: 'Wrath cookie duration',
  wrathCookieEffDur: 'Wrath cookie effect duration',
  wrathCookieFreq: 'Wrath cookie frequency',
  wrathCookieGain: 'Wrath cookie gains',
  wrinklerEat: 'Wrinkler ',
  wrinklerSpawn: 'Wrinkler spawn frequency',
};

;// ./src/Sim/ReplacedGameFunctions/SimHasAchiev.js


/**
 * This functions creates functions similarly to Game.HasAchiev but checks Sim Data instead of Game Data
 */
function SimHasAchiev(what) {
  return SimAchievements[what] ? SimAchievements[what].won : 0;
}

;// ./src/Sim/Calculations/CheckOtherAchiev.js






/**
 * This function calculates if any special achievements have been obtained
 * If so it SimWin()'s them and the caller function will know to recall CM.Sim.CalculateGains()
 * It is called at the end of any functions that simulates certain behaviour
 */
function CheckOtherAchiev() {
  let grandmas = 0;
  Object.keys(Game.GrandmaSynergies).forEach((i) => {
    if (SimHas(Game.GrandmaSynergies[i])) grandmas += 1;
  });
  if (!SimHasAchiev('Elder') && grandmas >= 7) SimWin('Elder');
  if (!SimHasAchiev('Veteran') && grandmas >= 14) SimWin('Veteran');

  let buildingsOwned = 0;
  let mathematician = 1;
  let base10 = 1;
  let minAmount = 100000;
  Object.keys(SimObjects).forEach((i) => {
    buildingsOwned += SimObjects[i].amount;
    minAmount = Math.min(SimObjects[i].amount, minAmount);
    if (!SimHasAchiev('Mathematician')) {
      if (
        SimObjects[i].amount <
        Math.min(128, 2 ** (Game.ObjectsById.length - Game.Objects[i].id - 1))
      )
        mathematician = 0;
    }
    if (!SimHasAchiev('Base 10')) {
      if (SimObjects[i].amount < (Game.ObjectsById.length - Game.Objects[i].id) * 10) base10 = 0;
    }
  });
  if (minAmount >= 1) SimWin('One with everything');
  if (mathematician === 1) SimWin('Mathematician');
  if (base10 === 1) SimWin('Base 10');
  if (minAmount >= 100) SimWin('Centennial');
  if (minAmount >= 150) SimWin('Centennial and a half');
  if (minAmount >= 200) SimWin('Bicentennial');
  if (minAmount >= 250) SimWin('Bicentennial and a half');
  if (minAmount >= 300) SimWin('Tricentennial');
  if (minAmount >= 350) SimWin('Tricentennial and a half');
  if (minAmount >= 400) SimWin('Quadricentennial');
  if (minAmount >= 450) SimWin('Quadricentennial and a half');
  if (minAmount >= 500) SimWin('Quincentennial');
  if (minAmount >= 550) SimWin('Quincentennial and a half');
  if (minAmount >= 600) SimWin('Sexcentennial');
  if (minAmount >= 650) SimWin('Sexcentennial and a half');
  if (minAmount >= 700) SimWin('Septcentennial');

  if (buildingsOwned >= 100) SimWin('Builder');
  if (buildingsOwned >= 500) SimWin('Architect');
  if (buildingsOwned >= 1000) SimWin('Engineer');
  if (buildingsOwned >= 2500) SimWin('Lord of Constructs');
  if (buildingsOwned >= 5000) SimWin('Grand design');
  if (buildingsOwned >= 7500) SimWin('Ecumenopolis');
  if (buildingsOwned >= 10000) SimWin('Myriad');

  if (SimUpgradesOwned >= 20) SimWin('Enhancer');
  if (SimUpgradesOwned >= 50) SimWin('Augmenter');
  if (SimUpgradesOwned >= 100) SimWin('Upgrader');
  if (SimUpgradesOwned >= 200) SimWin('Lord of Progress');
  if (SimUpgradesOwned >= 300) SimWin('The full picture');
  if (SimUpgradesOwned >= 400) SimWin("When there's nothing left to add");
  if (SimUpgradesOwned >= 500) SimWin('Kaizen');
  if (SimUpgradesOwned >= 600) SimWin('Beyond quality');
  if (SimUpgradesOwned >= 700) SimWin("Oft we mar what's well");

  if (buildingsOwned >= 4000 && SimUpgradesOwned >= 300) SimWin('Polymath');
  if (buildingsOwned >= 8000 && SimUpgradesOwned >= 400) SimWin('Renaissance baker');

  if (SimObjects.Cursor.amount + SimObjects.Grandma.amount >= 777) SimWin('The elder scrolls');

  let hasAllHalloCook = true;
  Object.keys(HalloCookies).forEach((i) => {
    if (!SimHas(HalloCookies[i])) hasAllHalloCook = false;
  });
  if (hasAllHalloCook) SimWin('Spooky cookies');

  let hasAllChristCook = true;
  Object.keys(ChristCookies).forEach((i) => {
    if (!SimHas(ChristCookies[i])) hasAllChristCook = false;
  });
  if (hasAllChristCook) SimWin('Let it snow');

  if (SimHas('Fortune cookies')) {
    const list = Game.Tiers.fortune.upgrades;
    let fortunes = 0;
    Object.keys(list).forEach((i) => {
      if (SimHas(list[i].name)) fortunes += 1;
    });
    if (fortunes >= list.length) SimWin('O Fortuna');
  }
}

;// ./src/Sim/SimulationEvents/BuyBuildingBonusIncome.js






/**
 * This function calculates the bonus income of buying a building
 * It is called by CM.Cache.CacheBuildingIncome()
 * @param	{string}	building	The name of the building to be bought
 * @param	{number}	amount		The amount to be bought
 * @returns {number}				The bonus income of the building
 */
function BuyBuildingsBonusIncome(building, amount) {
  CopyData();
  SimObjects[building].amount += amount;
  const me = SimObjects[building];

  if (building === 'Cursor') {
    if (me.amount >= 1) SimWin('Click');
    if (me.amount >= 2) SimWin('Double-click');
    if (me.amount >= 50) SimWin('Mouse wheel');
    if (me.amount >= 100) SimWin('Of Mice and Men');
    if (me.amount >= 200) SimWin('The Digital');
    if (me.amount >= 300) SimWin('Extreme polydactyly');
    if (me.amount >= 400) SimWin('Dr. T');
    if (me.amount >= 500) SimWin('Thumbs, phalanges, metacarpals');
    if (me.amount >= 600) SimWin('With her finger and her thumb');
    if (me.amount >= 700) SimWin('Gotta hand it to you');
    if (me.amount >= 800) SimWin("The devil's workshop");
    if (me.amount >= 900) SimWin('All on deck');
    if (me.amount >= 1000) SimWin('A round of applause');
  } else {
    Object.keys(Game.Objects[me.name].tieredAchievs).forEach((j) => {
      if (me.amount >= Game.Tiers[Game.Objects[me.name].tieredAchievs[j].tier].achievUnlock) {
        SimWin(Game.Objects[me.name].tieredAchievs[j].name);
      }
    });
  }

  const lastAchievementsOwned = SimAchievementsOwned;

  CalculateGains();

  CheckOtherAchiev();

  if (lastAchievementsOwned !== SimAchievementsOwned) {
    CalculateGains();
  }

  return SimCookiesPs - Game.cookiesPs;
}

;// ./src/Disp/Tooltips/TypesOfTooltips/Building.js













/**
 * This function adds extra info to the Building tooltips
 */
function Building() {
  let target = CacheObjects1;
  if (Game.buyBulk === 1) target = CacheObjects1;
  else if (Game.buyBulk === 10) target = CacheObjects10;
  else if (Game.buyBulk === 100) target = CacheObjects100;

  TooltipPrice = Game.Objects[TooltipName].bulkPrice;
  TooltipBonusIncome = target[TooltipName].bonus;

  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipBuildUpgrade === 1 &&
    Game.buyMode === 1
  ) {
    const tooltipBox = l('CMTooltipBorder');
    TooltipCreateCalculationSection(tooltipBox);

    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipBuildUpgrade ===
        1 &&
      Game.buyMode === 1
    ) {
      l('CMTooltipIncome').textContent = Beautify_Beautify(TooltipBonusIncome, 2);
      const increase = Math.round((TooltipBonusIncome / Game.cookiesPs) * 10000);
      if (Number.isFinite(increase) && increase !== 0) {
        l('CMTooltipIncome').textContent += ` (${increase / 100}% of income)`;
      } else {
        l('CMTooltipIncome').textContent += ` (<0${
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleSeparator
            ? ','
            : '.'
        }01% of income)`;
      }
      l('CMTooltipBorder').className = ColourTextPre + target[TooltipName].colour;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPDisplayTime)
        l('CMTooltipPP').textContent = FormatTime(target[TooltipName].pp);
      else l('CMTooltipPP').textContent = Beautify_Beautify(target[TooltipName].pp, 2);
      l('CMTooltipPP').className = ColourTextPre + target[TooltipName].colour;
      const timeColour = GetTimeColour(
        (TooltipPrice - (Game.cookies + GetWrinkConfigBank())) / GetCPS(),
      );
      l('CMTooltipTime').textContent = timeColour.text;
      if (timeColour.text === 'Done!' && Game.cookies < target[TooltipName].price) {
        l('CMTooltipTime').textContent = `${timeColour.text} (with Wrink)`;
      } else l('CMTooltipTime').textContent = timeColour.text;
      l('CMTooltipTime').className = ColourTextPre + timeColour.colour;
    }

    // Add "production left till next achievement"-row
    l('CMTooltipProductionLeftHeader').style.display = 'none';
    l('CMTooltipProductionLeft').style.display = 'none';

    // eslint-disable-next-line no-restricted-syntax
    for (const i of Object.keys(Game.Objects[TooltipName].productionAchievs)) {
      if (!Game.HasAchiev(Game.Objects[TooltipName].productionAchievs[i].achiev.name)) {
        const nextProductionAchiev = Game.Objects[TooltipName].productionAchievs[i];
        l('CMTooltipProductionLeftHeader').style.display = '';
        l('CMTooltipProductionLeft').style.display = '';
        l('CMTooltipProductionLeft').className = `CMTooltipValue ProdAchievement${TooltipName}`;
        l('CMTooltipProductionLeft').textContent = `${Beautify_Beautify(
          nextProductionAchiev.pow - SimObjects[TooltipName].totalCookies,
          15,
        )} cookies`;
        break;
      }
    }

    const ObjectsTillNext = CacheObjectsNextAchievement[TooltipName];
    if (ObjectsTillNext.AmountNeeded < 101) {
      l('CMTooltipNextAchievementHeader').style.display = '';
      l('CMTooltipNextAchievement').style.display = '';

      let PPOfAmount;
      if (Game.cookiesPs) {
        PPOfAmount =
          Math.max(ObjectsTillNext.price - (Game.cookies + GetWrinkConfigBank()), 0) /
            Game.cookiesPs +
          ObjectsTillNext.price /
            BuyBuildingsBonusIncome(TooltipName, ObjectsTillNext.AmountNeeded);
      } else
        PPOfAmount =
          ObjectsTillNext.price /
          BuyBuildingsBonusIncome(TooltipName, ObjectsTillNext.AmountNeeded);

      l('CMTooltipNextAchievement').textContent = `${Beautify_Beautify(
        ObjectsTillNext.AmountNeeded,
      )} more for ${Beautify_Beautify(ObjectsTillNext.price)}, PP `;
      const PPFrag = document.createElement('span');
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPDisplayTime)
        PPFrag.textContent = FormatTime(PPOfAmount);
      else PPFrag.textContent = Beautify_Beautify(PPOfAmount);
      PPFrag.className = ColourTextPre + ColourOfPP({ pp: PPOfAmount }, ObjectsTillNext.price);
      l('CMTooltipNextAchievement').appendChild(PPFrag);
    } else {
      l('CMTooltipNextAchievementHeader').style.display = 'none';
      l('CMTooltipNextAchievement').style.display = 'none';
    }
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Disp/HelperFunctions/CalculateSingleTileChances.js
/* eslint-disable guard-for-in */
/* eslint-disable no-continue */
/* eslint-disable no-restricted-syntax */
/* eslint-disable no-param-reassign */

/**
 * Calculates the possible plants for a tile after the next garden tick.
 *
 * @param {Object} minigame A reference to the garden minigame
 * @param {number} plantId The ID of the tile's current plant (-1 if empty)
 * @param {number} age The age of the tile's current plant (ignored if empty)
 * @param {Object[][]} neighResults The calculated results of each neighboring tile
 * @param {number[]} cardinals The indices of orthogonally adjacent tiles in `neighResults`
 * @param {number[]} tileBoosts The boosts to aging and weed spawning this tile is recieving from nearby tiles in the format `[ageMult, weedMult]`
 * @param {number} dragonBoost The current calculated value of the boost from the "Supreme Intellect" dragon aura
 * @returns {{plantId: number, isMature: boolean, p: number}[]} The possible resulting tile states and their probabilities
 */
function CalculateSingleTileChances(
  minigame,
  plantId,
  age,
  neighResults,
  cardinals,
  tileBoosts,
  dragonBoost,
) {
  const { getMuts, plants, plantsById, plantContam, soilsById, soil } = minigame;
  const soilWeedMult = soilsById[soil].weedMult;

  const epsilon = 1e-12;
  const futureStates = [];
  const AddOutcome = function (outcome) {
    if (outcome.p < epsilon) return;

    const existing = futureStates.find(
      (o) =>
        o.plantId === outcome.plantId &&
        (outcome.plantId === -1 || o.isMature === outcome.isMature),
    );
    if (existing) existing.p += outcome.p;
    else futureStates.push(outcome);
  };
  let runningP = 1;

  if (plantId !== -1) {
    // tile has plant
    const currentPlant = plantsById[plantId];

    const AgeThresholdP = function (multiplier, threshold) {
      // probability that plant's age increases by at least threshold
      const minAge = currentPlant.ageTick * multiplier;
      const maxAge = minAge + currentPlant.ageTickR * multiplier;

      if (Math.abs(maxAge - minAge) < epsilon) {
        if (minAge >= threshold) return 1;
        if (minAge < threshold - 1) return 0;
        return minAge - (threshold - 1);
      }

      if (threshold <= minAge) return 1;
      if (threshold - 1 >= maxAge) return 0;

      const lower = Math.max(minAge, threshold - 1);
      const upper = Math.min(maxAge, threshold);

      const a = 0.5 * (upper - (threshold - 1)) ** 2 - 0.5 * (lower - (threshold - 1)) ** 2;
      const b = Math.max(0, maxAge - Math.max(minAge, threshold));

      return (a + b) / (maxAge - minAge);
    };

    // death
    if (!currentPlant.immortal) {
      const deathP = AgeThresholdP(tileBoosts[0] * dragonBoost, 100 - age);
      AddOutcome({ plantId: -1, isMature: false, p: deathP * runningP });
      runningP -= deathP * runningP;
    }

    // contamination
    if (!currentPlant.noContam) {
      const contamChances = [];

      for (const key in plantContam) {
        let inclusionP = plantContam[key];
        if (plants[key].weed) inclusionP *= soilWeedMult;
        contamChances.push([key, inclusionP]);
      }

      let totalContamP = 0;
      for (const [key1, inclusionP1] of contamChances) {
        if (plants[key1].id === plantId || inclusionP1 === 0) continue;

        let hasNeighborP = 0;
        for (const i of cardinals) {
          let isNeighborP = 0;
          for (const o of neighResults[i]) {
            if (o.plantId === key1 && o.isMature) isNeighborP += o.p;
          }
          hasNeighborP += isNeighborP * (1 - hasNeighborP);
        }
        if (hasNeighborP < epsilon) continue;

        let q = [1];
        for (const [key2, inclusionP2] of contamChances) {
          if (key1 !== key2) {
            const newQ = Array(q.length + 1).fill(0);
            for (let k = 0; k < q.length; k++) {
              newQ[k] += q[k] * (1 - inclusionP2);
              newQ[k + 1] += q[k] * inclusionP2;
            }
            q = newQ;
          }
        }

        const E = q.reduce((acc, probXk, k) => acc + probXk / (1 + k), 0);
        const contamP = inclusionP1 * E * hasNeighborP * runningP;
        AddOutcome({ plantId: plants[key1].id, isMature: false, p: contamP });
        totalContamP += contamP;
      }
      runningP -= totalContamP;
    }

    // survival (remaining probability)
    const maturityP = AgeThresholdP(tileBoosts[0] * dragonBoost, currentPlant.mature - age);
    AddOutcome({ plantId, isMature: true, p: maturityP * runningP });
    AddOutcome({ plantId, isMature: false, p: (1 - maturityP) * runningP });
  } else {
    // tile is empty
    let noNeighborsChance = 1;
    neighResults.forEach((neighbor) => {
      let emptyChance = 0;
      const emptyOutcome = neighbor.find((outcome) => outcome.plantId === -1);
      if (emptyOutcome) emptyChance = emptyOutcome.p;
      noNeighborsChance *= emptyChance;
    });

    // weeds
    const weedChance = 0.002 * soilWeedMult * tileBoosts[1];
    AddOutcome({ plantId: 13, isMature: false, p: weedChance * noNeighborsChance });
    AddOutcome({ plantId: -1, isMature: false, p: (1 - weedChance) * noNeighborsChance });

    runningP -= noNeighborsChance;

    // mutation
    if (noNeighborsChance < 1) {
      let totalMutationP = 0;

      const CombineNeighbors = function (i = 0, current = [], comboP = 1, results = []) {
        if (i >= neighResults.length) {
          results.push({ tiles: current.slice(), comboP });
          return results;
        }

        for (const state of neighResults[i])
          CombineNeighbors(i + 1, [...current, state], comboP * state.p, results);

        return results;
      };

      const loopsBase = (soilsById[soil].key === 'woodchips' ? 3 : 1) * dragonBoost;
      for (const combo of CombineNeighbors()) {
        // possible combinations of neighboring tiles
        const neighs = {};
        const neighsM = {};

        for (const tile of combo.tiles) {
          if (tile.plantId === -1) continue;
          const { key } = plantsById[tile.plantId];
          neighs[key] = (neighs[key] || 0) + 1;
          if (tile.isMature) neighsM[key] = (neighsM[key] || 0) + 1;
        }

        const muts = getMuts(neighs, neighsM);

        let perLoopMutationP = 0; // probability that any mutation occurs on a single loop with this combo
        const mutationChances = [];
        for (const [key, mutValue] of muts) {
          let inclusionP = mutValue;
          if (plants[key].weed) inclusionP *= soilWeedMult;
          if (plants[key].weed || plants[key].fungus) inclusionP *= tileBoosts[1];
          if (inclusionP > 0) mutationChances.push([key, inclusionP]);
        }

        const perLoopMutations = [];
        for (const [key1, inclusionP1] of mutationChances) {
          let q = [1];
          for (const [key2, inclusionP2] of mutationChances) {
            if (key1 !== key2) {
              const newQ = Array(q.length + 1).fill(0);
              for (let k = 0; k < q.length; k++) {
                newQ[k] += q[k] * (1 - inclusionP2);
                newQ[k + 1] += q[k] * inclusionP2;
              }
              q = newQ;
            }
          }

          const E = q.reduce((acc, probXk, k) => acc + probXk / (1 + k), 0);
          const mutationP = inclusionP1 * E;
          perLoopMutationP += mutationP;
          perLoopMutations.push([key1, mutationP * combo.comboP * runningP]);
        }

        if (perLoopMutationP === 0) continue;

        let loopsBoost = 1;
        if (loopsBase > 1) {
          if (Number.isInteger(loopsBase)) {
            loopsBoost = (1 - (1 - perLoopMutationP) ** loopsBase) / perLoopMutationP;
          } else {
            const loopsFloor = Math.floor(loopsBase);
            const loopsFrac = loopsBase % 1;
            const boostN = (1 - (1 - perLoopMutationP) ** loopsFloor) / perLoopMutationP;
            const boostNp1 = (1 - (1 - perLoopMutationP) ** (loopsFloor + 1)) / perLoopMutationP;
            loopsBoost = (1 - loopsFrac) * boostN + loopsFrac * boostNp1;
          }
        }

        for (const [key, mutationP] of perLoopMutations) {
          AddOutcome({ plantId: plants[key].id, maturityP: 0, p: mutationP * loopsBoost });
          totalMutationP += mutationP * loopsBoost;
        }
      }

      runningP -= totalMutationP;
    }

    // nothing (remaining probability)
    AddOutcome({ plantId: -1, isMature: false, p: runningP });
  }

  const total = futureStates.reduce((sum, o) => sum + o.p, 0);
  if (Math.abs(total - 1) > 1e-9) {
    futureStates.forEach((o) => {
      o.p /= total;
    });
  }

  return futureStates;
}

;// ./src/Disp/HelperFunctions/CalculateAllPlotChances.js
/* eslint-disable no-continue */




/**
 * Calculates the possible plants for the next garden tick and updates **`CachePlotChances`** accordingly (expensive.)
 *
 * @param {Object} minigame a reference to the garden minigame
 * @param {number} auraMult the current value of the "Supreme Intellect" dragon aura multiplier
 */
function CalculateAllPlotChances(minigame, auraMult) {
  const { plantsById, soilsById, soil, isTileUnlocked, getTile } = minigame;
  const dragonBoost = 1 + 0.05 * auraMult;

  // calculate boosts from neighbors for next tick
  const boosts = [];
  for (let y = 0; y < 6; y++) {
    boosts[y] = [];
    for (let x = 0; x < 6; x++) boosts[y].push([1, 1]); // [aging, weed]
  }

  const ApplyMultsToNearbyTiles = function (x, y, range, mults) {
    for (let dy = -range; dy <= range; dy++) {
      for (let dx = -range; dx <= range; dx++) {
        if ((dx !== 0 || dy !== 0) && isTileUnlocked(x + dx, y + dy)) {
          boosts[y + dy][x + dx][0] *= mults[0];
          boosts[y + dy][x + dx][1] *= mults[1];
        }
      }
    }
  };

  for (let y = 0; y < 6; y++) {
    for (let x = 0; x < 6; x++) {
      const tile = getTile(x, y);
      if (tile[0] === 0) continue;

      let ageMult;
      let weedMult;
      let range;
      const id = tile[0] - 1;
      switch (id) {
        case 7:
          ageMult = 1.03;
          weedMult = 1;
          range = 1;
          break;
        case 31:
          ageMult = 1;
          weedMult = 0;
          range = 2;
          break;
        case 32:
          ageMult = 1;
          weedMult = 0;
          range = 1;
          break;
        case 33:
          ageMult = 0.5;
          weedMult = 1;
          range = 1;
          break;
        default:
          continue;
      }

      let mult = soilsById[soil].effMult;
      const matureAge = plantsById[id].mature;
      const stage = 1 + (tile[1] >= matureAge ? 3 : Math.floor(tile[1] / (matureAge * 0.333)));

      // eslint-disable-next-line default-case
      switch (stage) {
        case 1:
          mult *= 0.1;
          break;
        case 2:
          mult *= 0.25;
          break;
        case 3:
          mult *= 0.5;
          break;
      }

      if (ageMult > 1 || mult < 1) ageMult = (ageMult - 1) * mult + 1;
      else ageMult /= mult;

      ApplyMultsToNearbyTiles(x, y, range, [ageMult, weedMult]);
    }
  }

  // initialize all probabilities to current state
  const plotOutcomes = [[], [], [], [], [], []];

  for (let y = 0; y < 6; y++) {
    for (let x = 0; x < 6; x++) {
      if (!isTileUnlocked(x, y)) continue;

      const tile = getTile(x, y);
      if (tile[0] === 0) plotOutcomes[y][x] = [{ plantId: -1, isMature: false, p: 1 }];
      else {
        const plantId = tile[0] - 1;
        plotOutcomes[y][x] = [{ plantId, isMature: tile[1] >= plantsById[plantId].mature, p: 1 }];
      }
    }
  }

  // update each tile's chances
  for (let y = 0; y < 6; y++) {
    for (let x = 0; x < 6; x++) {
      if (!isTileUnlocked(x, y)) continue;

      // collect neighbor probabilities
      const neighResults = [];
      const cardinals = [];
      for (let dy = -1; dy <= 1; dy++)
        for (let dx = -1; dx <= 1; dx++) {
          if ((dx !== 0 || dy !== 0) && isTileUnlocked(x + dx, y + dy)) {
            neighResults.push(plotOutcomes[y + dy][x + dx]);
            if (dx === 0 || dy === 0) cardinals.push(neighResults.length - 1); // save indices of cardinal neighbors
          }
        }

      const tile = getTile(x, y);

      plotOutcomes[y][x] = CalculateSingleTileChances(
        minigame,
        tile[0] - 1,
        tile[1],
        neighResults,
        cardinals,
        boosts[y][x],
        dragonBoost,
      );

      // save results
      CachePlotChances[y][x] = [];

      const emptyP = plotOutcomes[y][x]
        .filter((o) => o.plantId === -1)
        .reduce((s, o) => s + o.p, 0);
      if (emptyP > 0) CachePlotChances[y][x].push({ plantId: -1, maturityP: 0, p: emptyP });

      for (let id = 0; id < plantsById.length; id++) {
        const matches = plotOutcomes[y][x].filter((o) => o.plantId === id);
        if (matches.length > 1) {
          const plantP = matches.reduce((s, o) => s + o.p, 0);
          const maturityP =
            matches.filter((o) => o.isMature === true).reduce((s, o) => s + o.p, 0) / plantP;
          CachePlotChances[y][x].push({ plantId: id, maturityP, p: plantP });
        } else if (matches.length === 1)
          CachePlotChances[y][x].push({
            plantId: id,
            maturityP: matches[0].isMature ? 1 : 0,
            p: matches[0].p,
          });
      }

      CachePlotChances[y][x].sort((a, b) => a.plantId - b.plantId);
    }
  }
}

;// ./src/Disp/Tooltips/TypesOfTooltips/GardenPlots.js
/* eslint-disable guard-for-in */
/* eslint-disable no-restricted-syntax */







/**
 * This function adds extra info to the garden plot tooltips
 * It adds to the additional information to l('CMTooltipArea')
 */
function GardenPlots() {
  const { minigame } = Game.Objects.Farm;
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipPlots) {
    const tooltipBorder = l('CMTooltipBorder');

    if (minigame.plot[TooltipName[1]][TooltipName[0]][0] !== 0) {
      const rewardTooltip = document.createElement('div');
      rewardTooltip.appendChild(TooltipCreateHeader('Reward (Current / Maximum)'));
      const mature =
        minigame.plot[TooltipName[1]][TooltipName[0]][1] >=
        minigame.plantsById[minigame.plot[TooltipName[1]][TooltipName[0]][0] - 1].mature;
      const plantName =
        minigame.plantsById[minigame.plot[TooltipName[1]][TooltipName[0]][0] - 1].name;
      const reward = document.createElement('div');
      reward.id = 'CMTooltipPlantReward';
      rewardTooltip.appendChild(reward);
      if (plantName === 'Chocoroot' || plantName === 'White chocoroot') {
        reward.textContent = `${
          mature ? Beautify_Beautify(Math.min(Game.cookies * 0.03, Game.cookiesPs * 60 * 3)) : '0'
        } / ${Beautify_Beautify(Game.cookiesPs * 60 * 3)}`;
      } else if (plantName === 'Bakeberry') {
        reward.textContent = `${
          mature ? Beautify_Beautify(Math.min(Game.cookies * 0.03, Game.cookiesPs * 60 * 30)) : '0'
        } / ${Beautify_Beautify(Game.cookiesPs * 60 * 30)}`;
      } else if (plantName === 'Queenbeet') {
        reward.textContent = `${
          mature ? Beautify_Beautify(Math.min(Game.cookies * 0.04, Game.cookiesPs * 60 * 60)) : '0'
        } / ${Beautify_Beautify(Game.cookiesPs * 60 * 60)}`;
      } else if (plantName === 'Duketater') {
        reward.textContent = `${
          mature ? Beautify_Beautify(Math.min(Game.cookies * 0.08, Game.cookiesPs * 60 * 120)) : '0'
        } / ${Beautify_Beautify(Game.cookiesPs * 60 * 120)}`;
      } else rewardTooltip.style.display = 'none';

      if (rewardTooltip.style.display !== 'none') tooltipBorder.appendChild(rewardTooltip);
    }

    if (
      minigame.parent.level !== CacheFarmLevel ||
      minigame.soil !== CacheGardenSoil ||
      Game.auraMult('Supreme Intellect') !== CacheSupremeIntellect
    ) {
      CacheFarmLevel = minigame.parent.level;
      CacheGardenSoil = minigame.soil;
      CacheSupremeIntellect = Game.auraMult('Supreme Intellect');
      CalculateAllPlotChances(minigame, CacheSupremeIntellect);
    }
    const plotChances = CachePlotChances[TooltipName[1]][TooltipName[0]];

    const plotTooltip = document.createElement('div');
    if (l('CMTooltipPlantReward')) plotTooltip.style.marginTop = '5px';
    plotTooltip.appendChild(TooltipCreateHeader('After Next Tick:'));

    const showIcon = [];
    for (const id in minigame.plantsById) {
      showIcon[id] = minigame.plantsById[id].unlocked !== 0;
      for (let y = 0; y < 6 && !showIcon[id]; y++) {
        for (let x = 0; x < 6; x++) {
          // eslint-disable-next-line eqeqeq
          if (minigame.plot[y][x][0] - 1 == id) {
            showIcon[id] = true;
            break;
          }
        }
      }
    }

    const tooltipOutcomes = document.createElement('div');
    const ConvertToPercentage = function (x) {
      if (x <= 0) return '0%';
      if (x >= 1) return '100%';

      const decimals =
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleDecimals + 1;
      const delta = 10 ** -decimals;

      const xH = x * 100;
      if (xH < delta) return `<${Beautify_Beautify(delta)}%`;
      if (xH > 100 - delta) return `>${Beautify_Beautify(100 - delta)}%`;

      return `${Beautify_Beautify(xH)}%`;
    };
    for (const outcome of plotChances) {
      const outcomeInfo = document.createElement('div');
      outcomeInfo.style.height = '48px';
      outcomeInfo.style.display = 'flex';
      outcomeInfo.style.alignItems = 'center';

      const outcomeIcon = document.createElement('img');
      outcomeIcon.style.float = 'left';
      outcomeIcon.style.objectFit = 'none';
      if (outcome.plantId === -1) {
        outcomeIcon.style.width = '40px';
        outcomeIcon.style.height = '40px';
        outcomeIcon.style.margin = '4px';
        outcomeIcon.src = `${Game.resPath}img/gardenPlots.png`;
        outcomeIcon.style.objectPosition = `${0 * -40}px ${0 * -40}px`;

        // add brown colour
        outcomeIcon.style.background = 'saddlebrown';
        outcomeIcon.style.maskImage = `url(${Game.resPath}img/gardenPlots.png)`;
      } else {
        outcomeIcon.style.width = '48px';
        outcomeIcon.style.height = '48px';
        outcomeIcon.style.margin = '0px';

        if (!showIcon[outcome.plantId]) {
          outcomeIcon.src = `${Game.resPath}img/icons.png?v=${Game.version}`;
          outcomeIcon.style.objectPosition = `${0 * -48}px ${7 * -48}px`; // question mark
        } else {
          outcomeIcon.src = `${Game.resPath}img/gardenPlants.png?v=${Game.version}`;
          outcomeIcon.style.objectPosition = `${4 * -48}px ${minigame.plantsById[outcome.plantId].icon * -48}px`;
        }
      }
      outcomeInfo.appendChild(outcomeIcon);

      const outcomeInfoText = document.createElement('div');
      outcomeInfoText.style.marginLeft = '5px';

      const outcomeProbability = document.createElement('div');
      outcomeProbability.textContent = ConvertToPercentage(outcome.p);
      outcomeInfoText.appendChild(outcomeProbability);

      if (outcome.plantId !== -1) {
        const outcomeMaturityChance = document.createElement('small');
        outcomeMaturityChance.innerHTML = `<small>${ConvertToPercentage(outcome.maturityP)} chance of being mature</small>`;
        outcomeInfoText.appendChild(outcomeMaturityChance);
      }

      outcomeInfo.appendChild(outcomeInfoText);
      tooltipOutcomes.appendChild(outcomeInfo);
    }
    plotTooltip.appendChild(tooltipOutcomes);
    tooltipBorder.appendChild(plotTooltip);
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Disp/HelperFunctions/CalculateStockNextExpectedValue.js
/**
 * This function calculates a stock's next expected value
 * @param	{number}	value		        The stock's current value
 * @param	{number}	delta			    The stock's current delta
 * @param	{number}	restingValue		The stock's resting value
 * @param	{number}	mode		        The stock's current mode
 * @param	{number}	bankLevel		    The bank building level
 * @param	{number}	dragonBoost		    The current aura multiplier from Supreme Intellect and Reality Bending
 * @returns	{number}	value + delta       The stock's next expected value
 */
function CalculateStockNextExpectedValue(
  pValue,
  pDelta,
  restingValue,
  mode,
  bankLevel,
  dragonBoost,
) {
  let value = pValue;
  let delta = pDelta;
  delta *= 0.97 + 0.01 * dragonBoost;
  switch (mode) {
    case 0:
      delta *= 0.95;
      break;
    case 1:
      delta *= 0.99;
      delta += 0.02;
      break;
    case 2:
      delta *= 0.99;
      delta -= 0.02;
      break;
    case 3:
      delta += 0.06;
      value += 2.5;
      break;
    case 4:
      delta -= 0.06;
      value -= 2.5;
      break;
    default:
      break;
  }
  value += (restingValue - value) * 0.01;
  if (mode === 3) value -= 0.582;
  if (mode === 4) value += 0.6;
  if (value > 100 + (bankLevel - 1) * 3 && delta > 0) delta *= 0.9;
  if (value < 5) value += (5 - value) * 0.5;
  if (value < 5 && delta < 0) delta *= 0.95;
  return Math.max(value + delta, 1);
}

;// ./src/Disp/Tooltips/TypesOfTooltips/StockMarket.js





/**
 * This function adds extra info to the stock market
 * It adds to the additional information to l('CMTooltipArea')
 */
function StockMarket() {
  const { minigame } = Game.Objects.Bank;
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipStocks) {
    const tooltipBox = l('CMTooltipBorder');
    const stock = minigame.goodsById[TooltipName];

    // Current stock mode
    tooltipBox.appendChild(TooltipCreateHeader('Current Mode'));
    const stockMode = document.createElement('div');
    stockMode.id = 'CMTooltipMode';
    tooltipBox.appendChild(stockMode);
    const modeIndex = stock.mode;
    const modes = ['Stable', 'Slow Rise', 'Slow Fall', 'Fast Rise', 'Fast Fall', 'Chaotic'];
    stockMode.textContent = modes[modeIndex];
    const colours = [ColourGray, ColourYellow, ColourOrange, ColourGreen, ColourRed, ColourPurple];
    stockMode.className = ColourTextPre + colours[modeIndex];

    // Current stock delta value
    tooltipBox.appendChild(TooltipCreateHeader('Delta'));
    const delta = document.createElement('div');
    delta.id = 'CMTooltipDelta';
    tooltipBox.appendChild(delta);
    delta.textContent = Beautify_Beautify(stock.d);
    const deltaColour = stock.d < 0 ? ColourRed : ColourGreen;
    delta.className = ColourTextPre + deltaColour;

    // Stock resting value
    tooltipBox.appendChild(TooltipCreateHeader('Resting Value'));
    const restingValue = document.createElement('div');
    restingValue.id = 'CMTooltipRestingValue';
    tooltipBox.appendChild(restingValue);
    restingValue.textContent = `$${Beautify_Beautify(minigame.getRestingVal(stock.id))}`;
    restingValue.style.color = 'white';

    // Next expected value
    tooltipBox.appendChild(TooltipCreateHeader('Expected Next Value'));
    const expectedNextValue = document.createElement('div');
    expectedNextValue.id = 'CMTooltipExpectedValue';
    tooltipBox.appendChild(expectedNextValue);
    const expectedValue = CalculateStockNextExpectedValue(
      stock.val,
      stock.d,
      minigame.getRestingVal(stock.id),
      stock.mode,
      Game.Objects.Bank.level,
      Game.auraMult('Supreme Intellect'),
    );
    expectedNextValue.textContent = `$${
      Beautify_Beautify(expectedValue) + (expectedValue < stock.val ? '\u25bc' : '\u25b2')
    }`;
    const expectedNextValueColour = expectedValue < stock.val ? ColourRed : ColourGreen;
    expectedNextValue.className = ColourTextPre + expectedNextValueColour;

    l('CMTooltipArea').appendChild(tooltipBox);
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Disp/HelperFunctions/CalculateGrimoireRefillTime.js
/**
 * This function calculates the time it takes to reach a certain magic level
 * @param	{number}	currentMagic		The current magic level
 * @param	{number}	maxMagic			The user's max magic level
 * @param	{number}	targetMagic			The target magic level
 * @returns	{number}	count / Game.fps	The time it takes to reach targetMagic
 */
function CalculateGrimoireRefillTime(currentMagic, maxMagic, targetMagic) {
  let magic = currentMagic;
  let count = 0;
  while (magic < targetMagic) {
    magic += Math.max(0.002, (magic / Math.max(maxMagic, 100)) ** 0.5) * 0.002;
    count += 1;
  }
  return count / Game.fps;
}

;// ./src/Disp/Tooltips/TypesOfTooltips/Grimoire.js






/**
 * This function adds extra info to the Grimoire tooltips
 * It adds to the additional information to l('CMTooltipArea')
 */
function Grimoire() {
  const { minigame } = Game.Objects['Wizard tower'];
  const spellCost = minigame.getSpellCost(minigame.spellsById[TooltipName]);

  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipGrim === 1 &&
    spellCost <= minigame.magicM
  ) {
    const tooltipBox = l('CMTooltipBorder');

    // Time left till enough magic for spell
    tooltipBox.appendChild(TooltipCreateHeader('Time Left'));
    const time = document.createElement('div');
    time.id = 'CMTooltipTime';
    tooltipBox.appendChild(time);
    const timeColour = GetTimeColour(
      CalculateGrimoireRefillTime(minigame.magic, minigame.magicM, spellCost),
    );
    time.textContent = timeColour.text;
    time.className = ColourTextPre + timeColour.colour;

    // Time left untill magic spent is recovered
    if (spellCost <= minigame.magic) {
      tooltipBox.appendChild(TooltipCreateHeader('Recover Time'));
      const recover = document.createElement('div');
      recover.id = 'CMTooltipRecover';
      tooltipBox.appendChild(recover);
      const recoverColour = GetTimeColour(
        CalculateGrimoireRefillTime(
          Math.max(0, minigame.magic - spellCost),
          minigame.magicM,
          minigame.magic,
        ),
      );
      recover.textContent = recoverColour.text;
      recover.className = ColourTextPre + recoverColour.colour;
    }

    // Extra information on cookies gained when spell is Conjure Baked Goods (Name === 0)
    if (TooltipName === '0') {
      tooltipBox.appendChild(TooltipCreateHeader('Cookies to be gained/lost'));
      const conjure = document.createElement('div');
      conjure.id = 'x';
      tooltipBox.appendChild(conjure);
      const reward = document.createElement('span');
      reward.style.color = '#33FF00';
      reward.textContent = Beautify_Beautify(
        Math.max(Math.min(Game.cookies * 0.15, Game.cookiesPs * 60 * 30), 7),
        2,
      );
      conjure.appendChild(reward);
      const seperator = document.createElement('span');
      seperator.textContent = ' / ';
      conjure.appendChild(seperator);
      const loss = document.createElement('span');
      loss.style.color = 'red';
      loss.textContent = Beautify_Beautify(
        Math.min(Game.cookies, Math.min(Game.cookies * 0.15, Game.cookiesPs * 60 * 15) + 13),
        2,
      );
      conjure.appendChild(loss);
    }

    l('CMTooltipArea').appendChild(tooltipBox);
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Disp/Tooltips/TypesOfTooltips/HarvestAll.js



/**
 * This function adds extra info to the Garden Harvest All tooltip
 * It is called when the Harvest All tooltip is created or refreshed by CM.Disp.UpdateTooltip()
 * It adds to the additional information to l('CMTooltipArea')
 */
function HarvestAll() {
  const { minigame } = Game.Objects.Farm;
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipLump) {
    l('CMTooltipBorder').appendChild(TooltipCreateHeader('Cookies gained from harvesting:'));
    let totalGain = 0;
    let mortal = 0;
    if (Game.keys[16] && Game.keys[17]) mortal = 1;
    for (let y = 0; y < 6; y++) {
      for (let x = 0; x < 6; x++) {
        if (minigame.plot[y][x][0] >= 1) {
          const tile = minigame.plot[y][x];
          const me = minigame.plantsById[tile[0] - 1];
          const plantName = me.name;

          let count = true;
          if (mortal && me.immortal) count = false;
          if (tile[1] < me.matureBase) count = false;
          if (count && plantName === 'Bakeberry') {
            totalGain += Math.min(Game.cookies * 0.03, Game.cookiesPs * 60 * 30);
          } else if ((count && plantName === 'Chocoroot') || plantName === 'White chocoroot') {
            totalGain += Math.min(Game.cookies * 0.03, Game.cookiesPs * 60 * 3);
          } else if (count && plantName === 'Queenbeet') {
            totalGain += Math.min(Game.cookies * 0.04, Game.cookiesPs * 60 * 60);
          } else if (count && plantName === 'Duketater') {
            totalGain += Math.min(Game.cookies * 0.08, Game.cookiesPs * 60 * 120);
          }
        }
      }
    }
    l('CMTooltipBorder').appendChild(document.createTextNode(Beautify_Beautify(totalGain)));
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Disp/Tooltips/TypesOfTooltips/PantheonGods.js





/**
 * This function adds extra info to the Pantheon Gods tooltip
 * It is called when the Harvest All tooltip is created or refreshed by CM.Disp.UpdateTooltip()
 * It adds to the additional information to l('CMTooltipArea')
 */
function PantheonGods() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipPantheon === 1) {
    const tooltipBox = l('CMTooltipBorder');
    let GodID;
    if (TooltipType === 'pas') GodID = TooltipName[1];
    else GodID = TooltipName;

    // Time left till enough magic for spell
    tooltipBox.appendChild(TooltipCreateHeader('Effect in position 1:'));
    const cps1 = document.createElement('div');
    cps1.id = 'CMPantheonTooltipPosition1';
    if (CacheGods[GodID][0] !== 0) {
      cps1.textContent = Beautify_Beautify(CacheGods[GodID][0]);
      const increase = Math.round((CacheGods[GodID][0] / Game.cookiesPs) * 10000);
      if (Number.isFinite(increase) && increase !== 0) {
        cps1.textContent += ` (${increase / 100}% of income)`;
      } else {
        cps1.textContent += ` (<0${
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleSeparator
            ? ','
            : '.'
        }01% of income)`;
      }
    } else cps1.textContent = 'No effect to CPS';
    tooltipBox.appendChild(cps1);

    tooltipBox.appendChild(TooltipCreateHeader('Effect in position 2:'));
    const cps2 = document.createElement('div');
    cps2.id = 'CMPantheonTooltipPosition2';
    if (CacheGods[GodID][1] !== 0) {
      cps2.textContent = Beautify_Beautify(CacheGods[GodID][1]);
      const increase = Math.round((CacheGods[GodID][1] / Game.cookiesPs) * 10000);
      if (Number.isFinite(increase) && increase !== 0) {
        cps2.textContent += ` (${increase / 100}% of income)`;
      } else {
        cps2.textContent += ` (<0${
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleSeparator
            ? ','
            : '.'
        }01% of income)`;
      }
    } else cps2.textContent = 'No effect to CPS';
    tooltipBox.appendChild(cps2);

    tooltipBox.appendChild(TooltipCreateHeader('Effect in position 3:'));
    const cps3 = document.createElement('div');
    cps3.id = 'CMPantheonTooltipPosition2';
    if (CacheGods[GodID][2] !== 0) {
      cps3.textContent = Beautify_Beautify(CacheGods[GodID][2]);
      const increase = Math.round((CacheGods[GodID][2] / Game.cookiesPs) * 10000);
      if (Number.isFinite(increase) && increase !== 0) {
        cps3.textContent += ` (${increase / 100}% of income)`;
      } else {
        cps3.textContent += ` (<0${
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleSeparator
            ? ','
            : '.'
        }01% of income)`;
      }
    } else cps3.textContent = 'No effect to CPS';
    tooltipBox.appendChild(cps3);

    l('CMTooltipArea').appendChild(tooltipBox);
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Disp/HelperFunctions/GetLumpColour.js


/**
 * This function returns Name and Colour as object for sugar lump type that is given as input param.
 * It is called by CM.Disp.UpdateTooltipSugarLump()
 * @param 	{string} 				type 			Sugar Lump Type.
 * @returns {{string}, {string}}	text, colour		An array containing the text and display-colour of the sugar lump
 */
function GetLumpColour(type) {
  if (type === 0) {
    return { text: 'Normal', colour: ColourGray };
  }
  if (type === 1) {
    return { text: 'Bifurcated', colour: ColourGreen };
  }
  if (type === 2) {
    return { text: 'Golden', colour: ColourYellow };
  }
  if (type === 3) {
    return { text: 'Meaty', colour: ColourOrange };
  }
  if (type === 4) {
    return { text: 'Caramelized', colour: ColourPurple };
  }
  return { text: 'Unknown Sugar Lump', colour: ColourRed };
}

;// ./src/Disp/Tooltips/TypesOfTooltips/SugarLump.js



/**
 * This function adds extra info to the Sugar Lump tooltip
 * It adds to the additional information to l('CMTooltipArea')
 */
function SugarLump() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipLump === 1) {
    const tooltipBox = l('CMTooltipBorder');

    tooltipBox.appendChild(TooltipCreateHeader('Current Sugar Lump'));

    const lumpType = document.createElement('div');
    lumpType.id = 'CMTooltipTime';
    tooltipBox.appendChild(lumpType);
    const lumpColour = GetLumpColour(Game.lumpCurrentType);
    lumpType.textContent = lumpColour.text;
    lumpType.className = ColourTextPre + lumpColour.colour;
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Disp/Tooltips/TypesOfTooltips/Upgrade.js










/**
 * This function adds extra info to the Upgrade tooltips
 */
function Upgrade() {
  const tooltipBox = l('CMTooltipBorder');
  TooltipCreateCalculationSection(tooltipBox);

  // Under autoplay, click and golden cookie upgrades carry their autoplay value
  const { autoValue } = CacheUpgrades[Game.UpgradesInStore[TooltipName].name];
  TooltipBonusIncome =
    typeof autoValue !== 'undefined'
      ? autoValue
      : CacheUpgrades[Game.UpgradesInStore[TooltipName].name].bonus;
  TooltipPrice = Game.Upgrades[Game.UpgradesInStore[TooltipName].name].getPrice();
  TooltipBonusMouse = CacheUpgrades[Game.UpgradesInStore[TooltipName].name].bonusMouse;

  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipBuildUpgrade === 1
  ) {
    l('CMTooltipIncome').textContent = Beautify_Beautify(TooltipBonusIncome, 2);
    const increase = Math.round((TooltipBonusIncome / Game.cookiesPs) * 10000);
    // Don't display certain parts of tooltip if not applicable
    if (l('CMTooltipIncome').textContent === '0') {
      l('Bonus IncomeTitle').style.display = 'none';
      l('CMTooltipIncome').style.display = 'none';
      l('Payback PeriodTitle').style.display = 'none';
      l('CMTooltipPP').style.display = 'none';
    } else {
      if (Number.isFinite(increase) && increase !== 0) {
        l('CMTooltipIncome').textContent += ` (${increase / 100}% of income)`;
      } else {
        l('CMTooltipIncome').textContent += ` (<0${
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ScaleSeparator
            ? ','
            : '.'
        }01% of income)`;
      }
      if (typeof autoValue !== 'undefined') l('CMTooltipIncome').textContent += ' with autoplay';
      l('CMTooltipBorder').className =
        ColourTextPre + CacheUpgrades[Game.UpgradesInStore[TooltipName].name].colour;
    }

    // If clicking power upgrade
    if (TooltipBonusMouse) {
      l('CMTooltipCookiePerClick').textContent = Beautify_Beautify(TooltipBonusMouse);
      l('CMTooltipCookiePerClick').style.display = 'block';
      l('CMTooltipCookiePerClick').previousSibling.style.display = 'block';
    }
    // If only a clicking power upgrade change PP to click-based period
    if (!TooltipBonusIncome && TooltipBonusMouse) {
      l('CMTooltipPP').textContent = `${Beautify_Beautify(TooltipPrice / TooltipBonusMouse)} Clicks`;
      l('CMTooltipPP').style.color = 'white';
      l('Payback PeriodTitle').style.display = 'block';
      l('CMTooltipPP').style.display = 'block';
    } else {
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPDisplayTime)
        l('CMTooltipPP').textContent = FormatTime(
          CacheUpgrades[Game.UpgradesInStore[TooltipName].name].pp,
        );
      else
        l('CMTooltipPP').textContent = Beautify_Beautify(
          CacheUpgrades[Game.UpgradesInStore[TooltipName].name].pp,
          2,
        );
      l('CMTooltipPP').className =
        ColourTextPre + CacheUpgrades[Game.UpgradesInStore[TooltipName].name].colour;
    }
    const timeColour = GetTimeColour(
      (TooltipPrice - (Game.cookies + GetWrinkConfigBank())) / GetCPS(),
    );
    l('CMTooltipTime').textContent = timeColour.text;
    if (
      timeColour.text === 'Done!' &&
      Game.cookies < Game.UpgradesInStore[TooltipName].getPrice()
    ) {
      l('CMTooltipTime').textContent = `${timeColour.text} (with Wrink)`;
    } else l('CMTooltipTime').textContent = timeColour.text;
    l('CMTooltipTime').className = ColourTextPre + timeColour.colour;

    // Add extra info to Chocolate egg tooltip
    if (Game.UpgradesInStore[TooltipName].name === 'Chocolate egg') {
      l('CMTooltipBorder').lastChild.style.marginBottom = '4px';
      l('CMTooltipBorder').appendChild(
        TooltipCreateHeader('Cookies to be gained (Currently/Max)'),
      );
      const chocolate = document.createElement('div');
      chocolate.style.color = 'white';
      chocolate.textContent = `${Beautify_Beautify(Game.cookies * 0.05)} / ${Beautify_Beautify(CacheLastChoEgg)}`;
      l('CMTooltipBorder').appendChild(chocolate);
    }
  } else l('CMTooltipArea').style.display = 'none';
}

;// ./src/Config/Toggles/ToggleToolWarnPos.js
/**
 * This function toggles the position of the warnings created by CM.Disp.TooltipCreateWarningSection()
 * It is called by a change in CM.Options.ToolWarnPos
 * and upon creation of the warning tooltip by CM.Disp.UpdateTooltipWarnings()
 */
function ToggleToolWarnPos() {
  if (l('CMDispTooltipWarningParent') !== null) {
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnPos === 0) {
      l('CMDispTooltipWarningParent').style.top = 'auto';
      l('CMDispTooltipWarningParent').style.margin = '4px -4px';
      l('CMDispTooltipWarningParent').style.padding = '3px 4px';
    } else {
      l('CMDispTooltipWarningParent').style.right = 'auto';
      l('CMDispTooltipWarningParent').style.margin = '4px';
      l('CMDispTooltipWarningParent').style.padding = '4px 3px';
    }
  }
}

;// ./src/Disp/Tooltips/TypesOfTooltips/Warnings.js










/**
 * This function updates the warnings section of the building and upgrade tooltips
 */
function Warnings() {
  if (TooltipType === 'b' || TooltipType === 'u') {
    if (document.getElementById('CMDispTooltipWarningParent') === null) {
      l('tooltipAnchor').appendChild(TooltipCreateWarningSection());
      ToggleToolWarnPos();
    }

    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnPos === 0)
      l('CMDispTooltipWarningParent').style.right = '0px';
    else l('CMDispTooltipWarningParent').style.top = `${l('tooltip').offsetHeight}px`;

    l('CMDispTooltipWarningParent').style.width = `${l('tooltip').offsetWidth - 6}px`;

    const amount = Game.cookies + GetWrinkConfigBank() - TooltipPrice;
    const bonusIncomeUsed = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings
      .ToolWarnBon
      ? TooltipBonusIncome
      : 0;
    let limitLucky = CacheLucky;
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnBon === 1) {
      let bonusNoFren = TooltipBonusIncome;
      bonusNoFren /= GetCPSBuffMult();
      limitLucky += (bonusNoFren * 60 * 15) / 0.15;
    }

    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnLucky === 1) {
      if (amount < limitLucky && (TooltipType !== 'b' || Game.buyMode === 1)) {
        l('CMDispTooltipWarnLucky').style.display = '';
        l('CMDispTooltipWarnLuckyText').textContent = `${Beautify_Beautify(
          limitLucky - amount,
        )} (${FormatTime((limitLucky - amount) / (GetCPS() + bonusIncomeUsed))})`;
      } else l('CMDispTooltipWarnLucky').style.display = 'none';
    } else l('CMDispTooltipWarnLucky').style.display = 'none';

    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnLuckyFrenzy === 1
    ) {
      const limitLuckyFrenzy = limitLucky * 7;
      if (amount < limitLuckyFrenzy && (TooltipType !== 'b' || Game.buyMode === 1)) {
        l('CMDispTooltipWarnLuckyFrenzy').style.display = '';
        l('CMDispTooltipWarnLuckyFrenzyText').textContent = `${Beautify_Beautify(
          limitLuckyFrenzy - amount,
        )} (${FormatTime((limitLuckyFrenzy - amount) / (GetCPS() + bonusIncomeUsed))})`;
      } else l('CMDispTooltipWarnLuckyFrenzy').style.display = 'none';
    } else l('CMDispTooltipWarnLuckyFrenzy').style.display = 'none';

    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnConjure === 1) {
      const limitConjure = limitLucky * 2;
      if (amount < limitConjure && (TooltipType !== 'b' || Game.buyMode === 1)) {
        l('CMDispTooltipWarnConjure').style.display = '';
        l('CMDispTooltipWarnConjureText').textContent = `${Beautify_Beautify(
          limitConjure - amount,
        )} (${FormatTime((limitConjure - amount) / (GetCPS() + bonusIncomeUsed))})`;
      } else l('CMDispTooltipWarnConjure').style.display = 'none';
    } else l('CMDispTooltipWarnConjure').style.display = 'none';

    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnConjureFrenzy ===
      1
    ) {
      const limitConjureFrenzy = limitLucky * 2 * 7;
      if (amount < limitConjureFrenzy && (TooltipType !== 'b' || Game.buyMode === 1)) {
        l('CMDispTooltipWarnConjureFrenzy').style.display = '';
        l('CMDispTooltipWarnConjureFrenzyText').textContent = `${Beautify_Beautify(
          limitConjureFrenzy - amount,
        )} (${FormatTime((limitConjureFrenzy - amount) / (GetCPS() + bonusIncomeUsed))})`;
      } else l('CMDispTooltipWarnConjureFrenzy').style.display = 'none';
    } else l('CMDispTooltipWarnConjureFrenzy').style.display = 'none';

    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnEdifice === 1 &&
      Game.Objects['Wizard tower'].minigameLoaded
    ) {
      if (CacheEdifice && amount < CacheEdifice && (TooltipType !== 'b' || Game.buyMode === 1)) {
        l('CMDispTooltipWarnEdifice').style.display = '';
        l('CMDispTooltipWarnEdificeText').textContent = `${Beautify_Beautify(
          CacheEdifice - amount,
        )} (${FormatTime((CacheEdifice - amount) / (GetCPS() + bonusIncomeUsed))})`;
      } else l('CMDispTooltipWarnEdifice').style.display = 'none';
    } else l('CMDispTooltipWarnEdifice').style.display = 'none';

    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnUser > 0) {
      if (
        amount <
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnUser *
            GetCPS() &&
        (TooltipType !== 'b' || Game.buyMode === 1)
      ) {
        l('CMDispTooltipWarnUser').style.display = '';
        // Need to update label text dynamically
        l('CMDispTooltipWarnUser').children[0].textContent =
          `${Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnUser}s of CPS`;
        l('CMDispTooltipWarnUserText').textContent = `${Beautify_Beautify(
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnUser *
            GetCPS() -
            amount,
        )} (${FormatTime(
          (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnUser *
            GetCPS() -
            amount) /
            (GetCPS() + bonusIncomeUsed),
        )})`;
      } else l('CMDispTooltipWarnUser').style.display = 'none';
    } else l('CMDispTooltipWarnUser').style.display = 'none';

    // Only show the box when at least one threshold is crossed
    const anyWarning = Array.from(l('CMDispTooltipWarnBox').children).some(
      (row) => row.className === 'CMWarnRow' && row.style.display !== 'none',
    );
    l('CMDispTooltipWarnBox').style.display = anyWarning ? '' : 'none';
  } else if (l('CMDispTooltipWarningParent') !== null) {
    l('CMDispTooltipWarningParent').remove();
  }
}

;// ./src/Disp/Tooltips/TypesOfTooltips/WrinklerButton.js





/**
 * This function adds extra info to the wrinkler button tooltip
 * It adds to the additional information to l('CMTooltipArea')
 */
function WrinklerButton() {
  l('tooltip').innerHTML = '';
  l('tooltip').appendChild(TooltipCreateHeader('Reward:'));

  const WrinklerReward = document.createElement('div');
  WrinklerReward.id = 'CMWrinklerReward';
  if (TooltipName === 'PopAllNormal') {
    WrinklerReward.textContent = Beautify_Beautify(CacheWrinklersNormal);
  } else if (TooltipName === 'PopFattest') {
    WrinklerReward.textContent = Beautify_Beautify(CacheWrinklersFattest[0]);
  }

  l('tooltip').appendChild(WrinklerReward);
}

;// ./src/Disp/Tooltips/UpdateTooltips.js














/**
 * This function updates the sections of the tooltips created by CookieMonster
 */
function UpdateTooltips() {
  CopyData();
  if (l('tooltipAnchor').style.display !== 'none' && l('CMTooltipArea')) {
    l('CMTooltipArea').innerHTML = '';
    const tooltipBox = TooltipCreateTooltipBox();
    l('CMTooltipArea').appendChild(tooltipBox);

    if (TooltipType === 'b') {
      Building();
    } else if (TooltipType === 'u') {
      Upgrade();
    } else if (TooltipType === 's') {
      SugarLump();
    } else if (TooltipType === 'g') {
      Grimoire();
    } else if (TooltipType === 'p') {
      GardenPlots();
    } else if (TooltipType === 'ha') {
      HarvestAll();
    } else if (TooltipType === 'sm') {
      StockMarket();
    } else if (TooltipType === 'wb') {
      WrinklerButton();
    } else if (TooltipType === 'pag' || (TooltipType === 'pas' && TooltipName[1] !== -1)) {
      PantheonGods();
    }
    Warnings();
  } else if (l('CMTooltipArea') === null) {
    // Remove warnings if its a basic tooltip
    if (l('CMDispTooltipWarningParent') !== null) {
      l('CMDispTooltipWarningParent').remove();
    }
  }
}

;// ./src/Disp/Tooltips/WrinklerTooltips.js




/**
 * This function checks and create a tooltip for the wrinklers
 * It is called by CM.Disp.Draw()
 * As wrinklers are not appended to the DOM we us a different system than for other tooltips
 */
function CheckWrinklerTooltip() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipWrink === 1 &&
    TooltipWrinklerArea === 1
  ) {
    // Latter is set by CM.Main.AddWrinklerAreaDetect
    let showingTooltip = false;
    Object.keys(Game.wrinklers).forEach((i) => {
      const me = Game.wrinklers[i];
      if (me.phase > 0 && me.selected) {
        showingTooltip = true;
        if (TooltipWrinklerBeingShown[i] === 0 || TooltipWrinklerBeingShown[i] === undefined) {
          const placeholder = document.createElement('div');
          const wrinkler = document.createElement('div');
          wrinkler.style.minWidth = '120px';
          wrinkler.style.marginBottom = '4px';
          const div = document.createElement('div');
          div.style.textAlign = 'center';
          div.id = 'CMTooltipWrinkler';
          wrinkler.appendChild(div);
          placeholder.appendChild(wrinkler);
          Game.tooltip.draw(this, escape(placeholder.innerHTML));
          TooltipWrinkler = i;
          TooltipWrinklerBeingShown[i] = 1;
        }
      } else {
        TooltipWrinklerBeingShown[i] = 0;
      }
    });
    if (!showingTooltip) {
      Game.tooltip.hide();
    }
  }
}

/**
 * This function updates the amount to be displayed by the wrinkler tooltip created by CM.Disp.CheckWrinklerTooltip()
 * It is called by CM.Disp.Draw()
 * As wrinklers are not appended to the DOM we us a different system than for other tooltips
 */
function UpdateWrinklerTooltip() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipWrink === 1 &&
    l('CMTooltipWrinkler') !== null
  ) {
    let { sucked } = Game.wrinklers[TooltipWrinkler];
    let toSuck = 1.1;
    if (Game.Has('Sacrilegious corruption')) toSuck *= 1.05;
    if (Game.wrinklers[TooltipWrinkler].type === 1) toSuck *= 3; // Shiny wrinklers
    sucked *= toSuck;
    if (Game.Has('Wrinklerspawn')) sucked *= 1.05;
    if (SimObjects.Temple.minigameLoaded) {
      const godLvl = Game.hasGod('scorn');
      if (godLvl === 1) sucked *= 1.15;
      else if (godLvl === 2) sucked *= 1.1;
      else if (godLvl === 3) sucked *= 1.05;
    }
    l('CMTooltipWrinkler').textContent = Beautify_Beautify(sucked);
  }
}

;// ./src/Disp/DrawHook.js










/**
 * This function handles all custom drawing for the Game.Draw() function.
 * It is hooked on 'draw' by CM.RegisterHooks()
 */
function CMDrawHook() {
  // Draw autosave timer in stats menu, this must be done here to make it count down correctly
  if (
    Game.prefs.autosave &&
    Game.drawT % 10 === 0 && // with autosave ON and every 10 ticks
    Game.onMenu === 'stats' &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Stats // while being on the stats menu only
  ) {
    const timer = document.getElementById('CMStatsAutosaveTimer');
    if (timer) {
      timer.innerText = Game.sayTime(Game.fps * 60 - (Game.T % (Game.fps * 60)), 4);
    }
  }

  // Update colours
  UpdateBuildings();
  UpdateUpgrades();
  UpdateUpgradeSectionsHeight();

  // Redraw timers
  UpdateTimerBar();

  // Update Bottom Bar
  UpdateBotBar();

  // Update Tooltip
  UpdateTooltips();

  // Update Wrinkler Tooltip
  CheckWrinklerTooltip();
  UpdateWrinklerTooltip();

  // Change menu refresh interval
  RefreshMenu();

  // Update display of wrinkler buttons, this checks if Elder Pledge has been bought and if they should be disabled
  ToggleWrinklerButtons();
}

;// ./src/Main/ClickHook.js


function CMClickHook() {
  // Add cookies from click to array that stores average
  CacheAverageCookiesFromClicks.addLatest(Game.computedMouseCps);
}

;// ./src/Cache/CPS/AverageQueue.js



/**
 * @class
 * @classdesc 	This is a class used to store values used to calculate average over time (mostly cps)
 * @var			{number}				maxLength	The maximum length of the value-storage
 * @var			{[]}					queue		The values stored
 * @method		addLatest(newValue)		Appends newValue to the value storage
 * @method		calcAverage(timePeriod)	Returns the average over the specified timeperiod
 */
class CMAvgQueue {
  constructor(maxLength) {
    this.maxLength = maxLength;
    this.queue = [];
  }

  addLatest(newValue) {
    if (this.queue.push(newValue) > this.maxLength) {
      this.queue.shift();
    }
  }

  /**
   * This functions returns the average of the values in the queue
   * @param 	{number}	timePeriod	The period in seconds to computer average over
   * @returns {number}	ret			The average
   */
  calcAverage(timePeriod) {
    let time = timePeriod;
    if (time > this.maxLength) time = this.maxLength;
    if (time > this.queue.length) time = this.queue.length;
    let ret = 0;
    for (let i = this.queue.length - 1; i >= 0 && i > this.queue.length - 1 - time; i--) {
      ret += this.queue[i];
    }
    if (ret === 0) {
      return 0;
    }
    return ret / time;
  }

  calcSum(timePeriod) {
    let time = timePeriod;
    if (time > this.maxLength) time = this.maxLength;
    if (time > this.queue.length) time = this.queue.length;
    if (time === 0) return 0;
    return this.queue.slice(-time).reduce((a, b) => a + b, 0);
  }
}

/**
 * This functions caches creates the CMAvgQueue used by CM.Cache.CacheAvgCPS() to calculate CPS
 * Called by CM.Cache.InitCache()
 */
function InitCookiesDiff() {
  CookiesDiff = new CMAvgQueue(CookieTimes[CookieTimes.length - 1]);
  WrinkDiff = new CMAvgQueue(CookieTimes[CookieTimes.length - 1]);
  WrinkFattestDiff = new CMAvgQueue(CookieTimes[CookieTimes.length - 1]);
  ChoEggDiff = new CMAvgQueue(CookieTimes[CookieTimes.length - 1]);
  ClicksDiff = new CMAvgQueue(ClickTimes[ClickTimes.length - 1]);
}

;// ./src/Cache/CPS/CPS.js




/**
 * This functions caches two variables related average CPS and Clicks
 * It is called by CM.Cache.LoopCache()
 * @global	{number}	CM.Cache.RealCookiesEarned	Cookies earned including the Chocolate Egg
 * @global	{number}	CM.Cache.AvgCPS				Average cookies over time-period as defined by AvgCPSHist
 * @global	{number}	CM.Cache.AverageClicks		Average cookies from clicking over time-period as defined by AvgClicksHist
 * @global	{number}	CM.Cache.AvgCPSChoEgg		Average cookies from combination of normal CPS and average Chocolate Cookie CPS
 */
function CacheAvgCPS() {
  const currDate = Math.floor(Date.now() / 1000);
  // Only calculate every new second
  if ((Game.T / Game.fps) % 1 === 0) {
    let choEggTotal = Game.cookies + CacheSellForChoEgg;
    if (Game.cpsSucked > 0) choEggTotal += CacheWrinklersTotal;
    CacheRealCookiesEarned = Math.max(Game.cookiesEarned, choEggTotal);
    choEggTotal *= 0.05;

    // Add recent gains to AvgQueue's
    // Income is measured on cookiesEarned, which spending does not lower; measuring the bank would
    // count every second in which something was bought as a second without income
    const timeDiff = currDate - CacheLastCPSCheck;
    const bankDiffAvg = Math.max(0, Game.cookiesEarned - CacheLastCookies) / timeDiff;
    const wrinkDiffAvg = Math.max(0, CacheWrinklersTotal - CacheLastWrinkCookies) / timeDiff;
    const wrinkFattestDiffAvg =
      Math.max(0, CacheWrinklersFattest[0] - CacheLastWrinkFattestCookies) / timeDiff;
    const choEggDiffAvg = Math.max(0, choEggTotal - CacheLastChoEgg) / timeDiff;
    const clicksDiffAvg = (Game.cookieClicks - CacheLastClicks) / timeDiff;
    for (let i = 0; i < timeDiff; i++) {
      CookiesDiff.addLatest(bankDiffAvg);
      WrinkDiff.addLatest(wrinkDiffAvg);
      WrinkFattestDiff.addLatest(wrinkFattestDiffAvg);
      ChoEggDiff.addLatest(choEggDiffAvg);
      ClicksDiff.addLatest(clicksDiffAvg);
    }

    // Store current data for next loop
    CacheLastCPSCheck = currDate;
    CacheLastCookies = Game.cookiesEarned;
    CacheLastWrinkCookies = CacheWrinklersTotal;
    CacheLastWrinkFattestCookies = CacheWrinklersFattest[0];
    CacheLastChoEgg = choEggTotal;
    CacheLastClicks = Game.cookieClicks;

    // Get average gain over period of cpsLength seconds
    const cpsLength =
      CookieTimes[Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgCPSHist];
    CacheAverageGainBank = CookiesDiff.calcAverage(cpsLength);
    CacheAverageGainWrink = WrinkDiff.calcAverage(cpsLength);
    CacheAverageGainWrinkFattest = WrinkFattestDiff.calcAverage(cpsLength);
    CacheAverageGainChoEgg = ChoEggDiff.calcAverage(cpsLength);
    CacheAverageCPS = CacheAverageGainBank;
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 1)
      CacheAverageCPS += CacheAverageGainWrink;
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 2)
      CacheAverageCPS += CacheAverageGainWrinkFattest;

    const choEgg = Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg');

    if (
      choEgg ||
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 0
    ) {
      CacheAvgCPSWithChoEgg =
        CacheAverageGainBank + CacheAverageGainWrink + (choEgg ? CacheAverageGainChoEgg : 0);
    } else CacheAvgCPSWithChoEgg = CacheAverageCPS;

    CacheAverageClicks = ClicksDiff.calcAverage(
      ClickTimes[Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgClicksHist],
    );
  }

  FillCMDCache({
    CacheRealCookiesEarned: CacheRealCookiesEarned,
    CacheLastCPSCheck: CacheLastCPSCheck,
    CacheLastCookies: CacheLastCookies,
    CacheLastWrinkCookies: CacheLastWrinkCookies,
    CacheLastWrinkFattestCookies: CacheLastWrinkFattestCookies,
    CacheLastChoEgg: CacheLastChoEgg,
    CacheLastClicks: CacheLastClicks,
    CacheAverageGainBank: CacheAverageGainBank,
    CacheAverageGainWrink: CacheAverageGainWrink,
    CacheAverageGainWrinkFattest: CacheAverageGainWrinkFattest,
    CacheAverageGainChoEgg: CacheAverageGainChoEgg,
    CacheAverageCPS: CacheAverageCPS,
    CacheAvgCPSWithChoEgg: CacheAvgCPSWithChoEgg,
    CacheAverageClicks: CacheAverageClicks,
  });
}

;// ./src/Sim/Calculations/NoGoldenSwitchCalc.js




/**
 * This function calculates CPS without the Golden Switch
 * It is called by CM.Cache.NoGoldSwitchCPS()
 */
function CalcNoGoldSwitchCPS() {
  CopyData();
  SimUpgrades['Golden switch [off]'].bought = 0;
  CalculateGains();
  return SimCookiesPs;
}

;// ./src/Cache/CPS/NoGoldSwitchCPS.js




/**
 * This function calculates CPS without the Golden Switch as it might be needed in other functions
 * If so it CM.Sim.Win()'s them and the caller function will know to recall CM.Sim.CalculateGains()
 * It is called at the end of any functions that simulates certain behaviour
 */
function CacheNoGoldSwitchCPS() {
  if (Game.Has('Golden switch [off]')) {
    CacheNoGoldSwitchCookiesPS = CalcNoGoldSwitchCPS();
  } else CacheNoGoldSwitchCookiesPS = Game.cookiesPs;

  FillCMDCache({ CacheNoGoldSwitchCookiesPS: CacheNoGoldSwitchCookiesPS });
}

;// ./src/Sim/SimulationEvents/BuyBuilding.js
/**
 * This function calculates the total price for buying "increase" of a building
 * @param	{string}	build		Name of the building
 * @param	{number}	basePrice	Base Price of building
 * @param	{number}	start		Starting amount of building
 * @param	{number}	free		Free amount of building
 * @param	{number}	increase	Increase of building
 * @returns {number}	moni		Total price
 */
function BuildingGetPrice(build, basePrice, start, free, increase) {
  let partialPrice = 0;
  for (let i = Math.max(0, start); i < Math.max(0, start + increase); i++) {
    partialPrice += Game.priceIncrease ** Math.max(0, i - free);
  }
  let price = basePrice * partialPrice;
  price = Game.modifyBuildingPrice(Game.Objects[build], price);
  return Math.ceil(price);
}

;// ./src/Cache/PP/Building.js







/**
 * This functions caches the buildings of bulk-buy mode when PP is compared against optimal single-purchase building
 * It saves all date in CM.Cache.Objects...
 * It is called by CM.Cache.CacheBuildingsPP()
 */
function CacheColour(target, amount) {
  Object.keys(target).forEach((i) => {
    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPRigidelMode &&
      amount === 1
    ) {
      target[i].colour = ColourGray; // eslint-disable-line no-param-reassign
      return;
    }
    // eslint-disable-next-line no-param-reassign
    target[i].colour = ColourOfPP(
      target[i],
      BuildingGetPrice(
        i,
        Game.Objects[i].basePrice,
        Game.Objects[i].amount,
        Game.Objects[i].free,
        amount,
      ),
    );
    // Colour based on excluding certain top-buildings
    for (
      let j = 0;
      j < Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPExcludeTop;
      j++
    ) {
      if (target[i].pp === CachePPArray[j][0]) target[i].colour = ColourGray; // eslint-disable-line no-param-reassign
    }
  });
}

function CachePP(target, amount) {
  Object.keys(target).forEach((i) => {
    const price = BuildingGetPrice(
      i,
      Game.Objects[i].basePrice,
      Game.Objects[i].amount,
      Game.Objects[i].free,
      amount,
    );
    if (Game.cookiesPs) {
      target[i].pp = // eslint-disable-line no-param-reassign
        Math.max(price - (Game.cookies + GetWrinkConfigBank()), 0) / Game.cookiesPs +
        price / target[i].bonus;
    } else target[i].pp = price / target[i].bonus; // eslint-disable-line no-param-reassign
    if (
      !(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPRigidelMode &&
        amount === 1
      )
    )
      CachePPArray.push([target[i].pp, amount, price]);
  });
}

/**
 * This functions caches the PP of each building it saves all date in CM.Cache.Objects...
 * It is called by CM.Cache.CachePP()
 */
function CacheBuildingsPP() {
  CacheMinPP = Infinity;
  CachePPArray = [];
  if (
    typeof Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPExcludeTop ===
    'undefined'
  )
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPExcludeTop = 0; // Otherwise breaks during initialization

  // Calculate PP and colours
  CachePP(CacheObjects1, 1);
  CachePP(CacheObjects10, 10);
  CachePP(CacheObjects100, 100);

  // Set CM.Cache.min to best non-excluded buidliung
  CachePPArray.sort((a, b) => a[0] - b[0]);
  let indexOfMin = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPExcludeTop;
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.PPOnlyConsiderBuyable) {
    while (CachePPArray[indexOfMin][2] > Game.cookies) {
      indexOfMin += 1;
      if (CachePPArray.length === indexOfMin + 1) {
        break;
      }
    }
  }
  CacheMinPP = CachePPArray[indexOfMin][0];
  CacheMinPPBulk = CachePPArray[indexOfMin][1];

  CacheColour(CacheObjects1, 1);
  CacheColour(CacheObjects10, 10);
  CacheColour(CacheObjects100, 100);

  FillCMDCache({ CacheMinPP: CacheMinPP, CacheMinPPBulk: CacheMinPPBulk, CachePPArray: CachePPArray });
}

;// ./src/Cache/PP/Upgrade.js





/**
 * This functions caches the PP of each upgrade and stores it in CM.Cache.Upgrades
 * With auto-click or auto golden cookies on, click and golden cookie upgrades are valued at what they
 * bring under autoplay (stored as autoValue) instead of being gray
 * It is called by CM.Cache.CachePP()
 */
function CacheUpgradePP() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const autoplay = settings.AutoClick || settings.AutoGolden;
  const income = autoplay ? AutoplayIncome() : Game.cookiesPs;
  const bank = Game.cookies + GetWrinkConfigBank();
  Object.keys(CacheUpgrades).forEach((i) => {
    const price = Game.Upgrades[i].getPrice();
    let value = CacheUpgrades[i].bonus;
    delete CacheUpgrades[i].autoValue;
    if (autoplay) {
      const autoValue = AutoplayUpgradeValue(i, CacheUpgrades[i], income, bank);
      if (autoValue > (value || 0)) {
        CacheUpgrades[i].autoValue = autoValue;
        value = autoValue;
      }
    }
    if (income) {
      CacheUpgrades[i].pp = Math.max(price - bank, 0) / income + price / value;
    } else CacheUpgrades[i].pp = price / value;
    if (Number.isNaN(CacheUpgrades[i].pp)) CacheUpgrades[i].pp = Infinity;

    CacheUpgrades[i].colour = ColourOfPP(CacheUpgrades[i], price);
  });
}

;// ./src/Cache/PP/PP.js
/**
 * Section: Functions related to caching PP */





/**
 * This functions caches the PP of each building and upgrade and stores it in the cache
 * It is called by CM.Cache.LoopCache() and CM.Cache.InitCache()
 */
function PP_CachePP() {
  CacheBuildingsPP();
  CacheUpgradePP();
  window.CookieMonsterData.Objects1 = JSON.parse(JSON.stringify(CacheObjects1));
  window.CookieMonsterData.Objects10 = JSON.parse(JSON.stringify(CacheObjects10));
  window.CookieMonsterData.Objects100 = JSON.parse(JSON.stringify(CacheObjects100));
  window.CookieMonsterData.Upgrades = [];
  Object.entries(CacheUpgrades).forEach((i) => {
    window.CookieMonsterData.Upgrades[i[0]] = JSON.parse(JSON.stringify(i[1]));
  });
}

;// ./src/Sim/SimulationEvents/BuyUpgrades.js










/**
 * This function calculates the cookies per click in the simulated state
 * It is called by CM.Sim.BuyUpgradesBonusIncome() when an upgrades has no bonus-income (and is thus a clicking-upgrade)
 * and by CM.Cache.CacheBuildingIncome()
 * @returns	{number}	out	The clicking power
 */
function MouseCps() {
  let add = 0;
  if (SimHas('Thousand fingers')) add += 0.1;
  if (SimHas('Million fingers')) add *= 5;
  if (SimHas('Billion fingers')) add *= 10;
  if (SimHas('Trillion fingers')) add *= 20;
  if (SimHas('Quadrillion fingers')) add *= 20;
  if (SimHas('Quintillion fingers')) add *= 20;
  if (SimHas('Sextillion fingers')) add *= 20;
  if (SimHas('Septillion fingers')) add *= 20;
  if (SimHas('Octillion fingers')) add *= 20;
  if (SimHas('Nonillion fingers')) add *= 20;
  if (SimHas('Decillion fingers')) add *= 20;
  if (SimHas('Undecillion fingers')) add *= 20;
  if (SimHas('Unshackled cursors')) add *= 25;
  let num = 0;
  Object.keys(SimObjects).forEach((i) => {
    num += SimObjects[i].amount;
  });
  num -= SimObjects.Cursor.amount;
  add *= num;

  // Can use SimCookiesPs as function is always called after CM.Sim.CalculateGains()
  if (SimHas('Plastic mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Iron mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Titanium mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Adamantium mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Unobtainium mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Eludium mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Wishalloy mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Fantasteel mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Nevercrack mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Armythril mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Technobsidian mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Plasmarble mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Miraculite mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Aetherice mouse')) add += SimCookiesPs * 0.01;
  if (SimHas('Omniplast mouse')) add += SimCookiesPs * 0.01;

  if (SimHas('Fortune #104')) add += SimCookiesPs * 0.01;

  let mult = 1;
  if (SimHas("Santa's helpers")) mult *= 1.1;
  if (SimHas('Cookie egg')) mult *= 1.1;
  if (SimHas('Halo gloves')) mult *= 1.1;
  if (SimHas('Dragon claw')) mult *= 1.03;

  if (SimHas('Aura gloves')) {
    mult *= 1 + 0.05 * Math.min(Game.Objects.Cursor.level, SimHas('Luminous gloves') ? 20 : 10);
  }

  mult *= SimEff('click');
  if (SimObjects.Temple.minigameLoaded) {
    if (SimHasGod) {
      const godLvl = SimHasGod('labor');
      if (godLvl === 1) mult *= 1.15;
      else if (godLvl === 2) mult *= 1.1;
      else if (godLvl === 3) mult *= 1.05;
    }
  }

  Object.keys(Game.buffs).forEach((i) => {
    if (typeof Game.buffs[i].multClick !== 'undefined') mult *= Game.buffs[i].multClick;
  });

  // if (CM.Sim.auraMult('Dragon Cursor')) mult*=1.05;
  mult *= 1 + SimAuraMult('Dragon Cursor') * 0.05;

  // No need to make this function a CM function
  let out =
    mult *
    Game.ComputeCps(
      1,
      SimHas('Reinforced index finger') +
        SimHas('Carpal tunnel prevention cream') +
        SimHas('Ambidextrous'),
      add,
    );

  out = Game.runModHookOnValue('cookiesPerClick', out);

  if (Game.hasBuff('Cursed finger')) out = Game.buffs['Cursed finger'].power;

  return out;
}

/**
 * This function calculates the bonus income of buying a building
 * It is called by CM.Cache.CacheBuildingIncome()
 * @param	{string}				building	The name of the upgrade to be bought
 * @returns {[{number, number}]}				The bonus income of the upgrade and the difference in MouseCPS
 */
function BuyUpgradesBonusIncome(upgrade) {
  if (
    Game.Upgrades[upgrade].pool === 'toggle' ||
    (Game.Upgrades[upgrade].bought === 0 &&
      Game.Upgrades[upgrade].unlocked &&
      Game.Upgrades[upgrade].pool !== 'prestige')
  ) {
    CopyData();
    if (SimUpgrades[upgrade].name === 'Shimmering veil [on]') {
      SimUpgrades['Shimmering veil [off]'].bought = 0;
    } else if (SimUpgrades[upgrade].name === 'Golden switch [on]') {
      SimUpgrades['Golden switch [off]'].bought = 0;
    } else {
      SimUpgrades[upgrade].bought = (SimUpgrades[upgrade].bought + 1) % 2;
    }
    if (Game.CountsAsUpgradeOwned(Game.Upgrades[upgrade].pool)) SimUpgradesOwned += 1;

    if (upgrade === 'Elder Pledge') {
      SimPledges += 1;
      if (SimPledges > 0) SimWin('Elder nap');
      if (SimPledges >= 5) SimWin('Elder slumber');
    } else if (upgrade === 'Elder Covenant') {
      SimWin('Elder calm');
    } else if (upgrade === 'Prism heart biscuits') {
      SimWin('Lovely cookies');
    } else if (upgrade === 'Heavenly key') {
      SimWin('Wholesome');
    }

    const lastAchievementsOwned = SimAchievementsOwned;

    CalculateGains();

    CheckOtherAchiev();

    if (lastAchievementsOwned !== SimAchievementsOwned) {
      CalculateGains();
    }

    const diffMouseCPS = MouseCps() - Game.computedMouseCps;
    if (diffMouseCPS) {
      return [SimCookiesPs - Game.cookiesPs, diffMouseCPS];
    }
    return [SimCookiesPs - Game.cookiesPs];
  }
  return [];
}

;// ./src/Cache/PriceAndIncome/PriceAndIncome.js
/** Section: Functions related to caching income */









/**
 * This functions starts the calculation/simulation of the bonus income of buildings
 * It is called by CM.Cache.CacheIncome()
 * @param	{amount}	amount	Amount to be bought
 * @parem	{string}	target	The target Cache object ("Objects1", "Objects10" or "Objects100")
 */
function CacheBuildingIncome(amount) {
  // Click power before buying, from the same simulation so that its approximations cancel out
  CopyData();
  CalculateGains();
  const mouseNow = MouseCps();
  const result = {};
  Object.keys(Game.Objects).forEach((i) => {
    result[i] = {};
    result[i].bonus = BuyBuildingsBonusIncome(i, amount);
    // The simulation still holds the purchase, so this is the click power it adds
    result[i].bonusMouse = MouseCps() - mouseNow;
    if (amount !== 1) {
      CacheDoRemakeBuildPrices = 1;
    }
  });
  return result;
}

/**
 * This functions starts the calculation/simulation of the bonus income of upgrades
 * It is called by CM.Cache.CacheIncome()
 */
function CacheUpgradeIncome() {
  CacheUpgrades = {};
  for (let i = 0; i < Game.UpgradesInStore.length; i++) {
    const upgradeName = Game.UpgradesInStore[i].name;
    const bonusIncome = BuyUpgradesBonusIncome(upgradeName);
    if (upgradeName === 'Elder Pledge') {
      CacheUpgrades[upgradeName] = {
        bonus: Game.cookiesPs - CacheAverageGainBank,
      };
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 1)
        CacheUpgrades[upgradeName].bonus -= CacheAverageGainWrink;
      else if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.CalcWrink === 2)
        CacheUpgrades[upgradeName].bonus -= CacheAverageGainWrinkFattest;
      if (!Number.isFinite(CacheUpgrades[upgradeName].bonus)) CacheUpgrades[upgradeName].bonus = 0;
    } else {
      CacheUpgrades[upgradeName] = {};
      if (bonusIncome[0]) CacheUpgrades[upgradeName].bonus = bonusIncome[0];
      if (bonusIncome[1]) CacheUpgrades[upgradeName].bonusMouse = bonusIncome[1];
    }
  }
}

/**
 * This functions caches the price of each building and stores it in the cache
 */
function CacheBuildingsPrices() {
  Object.keys(Game.Objects).forEach((i) => {
    CacheObjects1[i].price = BuildingGetPrice(
      i,
      Game.Objects[i].basePrice,
      Game.Objects[i].amount,
      Game.Objects[i].free,
      1,
    );
    CacheObjects10[i].price = BuildingGetPrice(
      i,
      Game.Objects[i].basePrice,
      Game.Objects[i].amount,
      Game.Objects[i].free,
      10,
    );
    CacheObjects100[i].price = BuildingGetPrice(
      i,
      Game.Objects[i].basePrice,
      Game.Objects[i].amount,
      Game.Objects[i].free,
      100,
    );
    CacheObjectsNextAchievement[i].price = BuildingGetPrice(
      i,
      Game.Objects[i].basePrice,
      Game.Objects[i].amount,
      Game.Objects[i].free,
      CacheObjectsNextAchievement[i].AmountNeeded,
    );
  });

  FillCMDCache({ CacheObjectsNextAchievement: CacheObjectsNextAchievement });
}

/**
 * This functions caches the income gain of each building and upgrade and stores it in the cache
 * It is called by CM.Main.Loop() and CM.Cache.InitCache()
 */
function CacheIncome() {
  // Simulate Building Buys for 1, 10 and 100 amount
  CacheObjects1 = CacheBuildingIncome(1);
  CacheObjects10 = CacheBuildingIncome(10);
  CacheObjects100 = CacheBuildingIncome(100);

  // Simulate Upgrade Buys
  CacheUpgradeIncome();
}

;// ./src/Cache/Stats/ChainCookies.js




/**
 * This functions calculates the max possible payout given a set of variables
 * It is called by CM.Disp.CreateStatsChainSection() and CM.Cache.CacheChain()
 * @param	{number}					digit		Number of Golden Cookies in chain
 * @param	{number}					maxPayout	Maximum payout
 * @param	{number}					mult		Multiplier
 * @returns	[{number, number, number}]				Total cookies earned, cookie needed for this and next level
 */
function MaxChainCookieReward(digit, maxPayout, mult) {
  let totalFromChain = 0;
  let moni = 0;
  let nextMoni = 0;
  let nextRequired = 0;
  let chain = 1 + Math.max(0, Math.ceil(Math.log(Game.cookies) / Math.LN10) - 10);
  while (nextMoni < maxPayout * mult) {
    moni = Math.max(
      digit,
      Math.min(Math.floor((1 / 9) * 10 ** chain * digit * mult), maxPayout * mult),
    );
    nextMoni = Math.max(
      digit,
      Math.min(Math.floor((1 / 9) * 10 ** (chain + 1) * digit * mult), maxPayout * mult),
    );
    nextRequired = Math.floor((1 / 9) * 10 ** (chain + 1) * digit * mult);
    totalFromChain += moni;
    chain += 1;
  }
  return [totalFromChain, moni, nextRequired];
}

/**
 * This functions caches data related to Chain Cookies reward from Golden Cookioes
 * It is called by CM.Main.Loop() upon changes to cps and CM.Cache.InitCache()
 * @global	[{number, number}]	CM.Cache.ChainMaxReward			Total cookies earned, and cookies needed for next level for normal chain
 * @global	{number}			CM.Cache.ChainRequired			Cookies needed for maximum reward for normal chain
 * @global	{number}			CM.Cache.ChainRequiredNext		Total cookies needed for next level for normal chain
 * @global	[{number, number}]	CM.Cache.ChainMaxWrathReward			Total cookies earned, and cookies needed for next level for wrath chain
 * @global	{number}			CM.Cache.ChainWrathRequired			Cookies needed for maximum reward for wrath chain
 * @global	{number}			CM.Cache.ChainWrathRequiredNext		Total cookies needed for next level for wrath chain
 * @global	[{number, number}]	CM.Cache.ChainFrenzyMaxReward			Total cookies earned, and cookies needed for next level for normal frenzy chain
 * @global	{number}			CM.Cache.ChainFrenzyRequired			Cookies needed for maximum reward for normal frenzy chain
 * @global	{number}			CM.Cache.ChainFrenzyRequiredNext		Total cookies needed for next level for normal frenzy chain
 * @global	[{number, number}]	CM.Cache.ChainFrenzyWrathMaxReward			Total cookies earned, and cookies needed for next level for wrath frenzy chain
 * @global	{number}			CM.Cache.ChainFrenzyWrathRequired			Cookies needed for maximum reward for wrath frenzy chain
 * @global	{number}			CM.Cache.ChainFrenzyWrathRequiredNext		Total cookies needed for next level for wrath frenzy chain
 */
function CacheChain() {
  let maxPayout = CacheNoGoldSwitchCookiesPS * 60 * 60 * 6 * CacheDragonsFortuneMultAdjustment;
  // Removes effect of Frenzy etc.
  const cpsBuffMult = GetCPSBuffMult();
  if (cpsBuffMult > 0) maxPayout /= cpsBuffMult;
  else maxPayout = 0;

  CacheChainMaxReward = MaxChainCookieReward(7, maxPayout, CacheGoldenCookiesMult);
  CacheChainRequired = (CacheChainMaxReward[1] * 2) / CacheGoldenCookiesMult;
  CacheChainRequiredNext = CacheChainMaxReward[2] / 60 / 60 / 6 / CacheDragonsFortuneMultAdjustment;

  CacheChainWrathMaxReward = MaxChainCookieReward(6, maxPayout, CacheWrathCookiesMult);
  CacheChainWrathRequired = (CacheChainWrathMaxReward[1] * 2) / CacheWrathCookiesMult;
  CacheChainWrathRequiredNext =
    CacheChainWrathMaxReward[2] / 60 / 60 / 6 / CacheDragonsFortuneMultAdjustment;

  CacheChainFrenzyMaxReward = MaxChainCookieReward(7, maxPayout * 7, CacheGoldenCookiesMult);
  CacheChainFrenzyRequired = (CacheChainFrenzyMaxReward[1] * 2) / CacheGoldenCookiesMult;
  CacheChainFrenzyRequiredNext =
    CacheChainFrenzyMaxReward[2] / 60 / 60 / 6 / CacheDragonsFortuneMultAdjustment;

  CacheChainFrenzyWrathMaxReward = MaxChainCookieReward(6, maxPayout * 7, CacheWrathCookiesMult);
  CacheChainFrenzyWrathRequired = (CacheChainFrenzyWrathMaxReward[1] * 2) / CacheWrathCookiesMult;
  CacheChainFrenzyWrathRequiredNext =
    CacheChainFrenzyWrathMaxReward[2] / 60 / 60 / 6 / CacheDragonsFortuneMultAdjustment;

  FillCMDCache({
    CacheChainMaxReward: CacheChainMaxReward,
    CacheChainRequired: CacheChainRequired,
    CacheChainRequiredNext: CacheChainRequiredNext,
    CacheChainWrathMaxReward: CacheChainWrathMaxReward,
    CacheChainWrathRequired: CacheChainWrathRequired,
    CacheChainWrathRequiredNext: CacheChainWrathRequiredNext,
    CacheChainFrenzyMaxReward: CacheChainFrenzyMaxReward,
    CacheChainFrenzyRequired: CacheChainFrenzyRequired,
    CacheChainFrenzyRequiredNext: CacheChainFrenzyRequiredNext,
    CacheChainFrenzyWrathMaxReward: CacheChainFrenzyWrathMaxReward,
    CacheChainFrenzyWrathRequired: CacheChainFrenzyWrathRequired,
    CacheChainFrenzyWrathRequiredNext: CacheChainFrenzyWrathRequiredNext,
  });
}

;// ./src/Cache/Stats/HeavenlyChips.js




/**
 * This functions caches the prestige levels ascending would grant and the rate at which they grow
 * It is called by CM.Cache.LoopCache()
 * @global	{number}	CM.Cache.LastHeavenlyChips	Prestige levels gained by ascending now
 * @global	{number}	CM.Cache.HCPerSecond		Heavenly chips gained per second at the current CPS
 */
function CacheHeavenlyChipsPS() {
  const total = Game.cookiesReset + Game.cookiesEarned;
  CacheLastHeavenlyChips =
    Math.floor(Game.HowMuchPrestige(total)) - Math.floor(Game.HowMuchPrestige(Game.cookiesReset));

  // Exact rate instead of differencing the floored level: d/dt cbrt(total / 1e12) = P / (3 * total) * CPS
  CacheHCPerSecond = total > 0 ? (Game.HowMuchPrestige(total) * GetCPS()) / (3 * total) : 0;

  FillCMDCache({ CacheLastHeavenlyChips: CacheLastHeavenlyChips, CacheHCPerSecond: CacheHCPerSecond });
}

;// ./src/Disp/MenuSections/Statistics/CreateMissingUpgrades.js
/** Functions related to displaying the missing upgrades in the Statistics page */



/**
 * This function creates the missing upgrades sections for prestige, normal and cookie upgrades
 */
function AddMissingUpgrades() {
  l('menu').childNodes.forEach((menuSection) => {
    if (menuSection.children[0]) {
      if (menuSection.children[0].innerHTML === 'Prestige' && CacheMissingUpgradesPrestige) {
        const prestigeUpgradesMissing = CacheMissingUpgradesPrestige.match(/div/g || 0).length / 2;
        const title = document.createElement('div');
        title.id = 'CMMissingUpgradesPrestigeTitle';
        title.className = 'listing';
        const titlefrag = document.createElement('div');
        titlefrag.innerHTML = `<b>Missing Prestige upgrades:</b> ${prestigeUpgradesMissing}/${
          Game.PrestigeUpgrades.length
        } (${Math.floor((prestigeUpgradesMissing / Game.PrestigeUpgrades.length) * 100)}%)`;
        title.appendChild(titlefrag);
        menuSection.appendChild(title);
        const upgrades = document.createElement('div');
        upgrades.className = 'listing crateBox';
        upgrades.innerHTML = CacheMissingUpgradesPrestige;
        menuSection.appendChild(upgrades);
      } else if (menuSection.children[0].innerHTML === 'Upgrades') {
        if (CacheMissingUpgrades) {
          const normalUpgradesMissing = CacheMissingUpgrades.match(/div/g || 0).length / 2;
          const title = document.createElement('div');
          title.id = 'CMMissingUpgradesTitle';
          title.className = 'listing';
          const titlefrag = document.createElement('div');
          titlefrag.innerHTML = `<b>Missing normal upgrades:</b> ${normalUpgradesMissing}/${
            Game.UpgradesByPool[''].length + Game.UpgradesByPool.tech.length
          } (${Math.floor(
            (normalUpgradesMissing /
              (Game.UpgradesByPool[''].length + Game.UpgradesByPool.tech.length)) *
              100,
          )}%)`;
          title.appendChild(titlefrag);
          menuSection.insertBefore(title, menuSection.childNodes[3]);
          const upgrades = document.createElement('div');
          upgrades.className = 'listing crateBox';
          upgrades.innerHTML = CacheMissingUpgrades;
          menuSection.insertBefore(
            upgrades,
            document.getElementById('CMMissingUpgradesTitle').nextSibling,
          );
        }
        if (CacheMissingUpgradesCookies) {
          const cookieUpgradesMissing = CacheMissingUpgradesCookies.match(/div/g || 0).length / 2;
          const title = document.createElement('div');
          title.id = 'CMMissingUpgradesCookiesTitle';
          title.className = 'listing';
          const titlefrag = document.createElement('div');
          titlefrag.innerHTML = `<b>Missing Cookie upgrades:</b> ${cookieUpgradesMissing}/${
            Game.UpgradesByPool.cookie.length
          } (${Math.floor((cookieUpgradesMissing / Game.UpgradesByPool.cookie.length) * 100)}%)`;
          title.appendChild(titlefrag);
          menuSection.appendChild(title);
          const upgrades = document.createElement('div');
          upgrades.className = 'listing crateBox';
          upgrades.innerHTML = CacheMissingUpgradesCookies;
          menuSection.appendChild(upgrades);
        }
      }
    }
  });
}

/**
 * This function returns the "crates" (icons) for missing upgrades in the stats sections
 * It returns a html string that gets appended to the respective CM.Cache.MissingUpgrades-variable by CM.Cache.CacheMissingUpgrades()
 * @param	{object}	me	The upgrade object
 * @returns	{string}	?	The HTML string that creates the icon.
 */
function crateMissing(me) {
  let classes = 'crate upgrade missing';
  if (me.pool === 'prestige') classes += ' heavenly';

  let noFrame = 0;
  if (!Game.prefs.crates) noFrame = 1;
  if (noFrame) classes += ' noFrame';

  let { icon } = me;
  if (me.iconFunction) icon = me.iconFunction();
  const tooltip = `function() {return Game.crateTooltip(Game.UpgradesById[${me.id}], 'stats');}`;
  return `<div class="${classes}"
	${Game.getDynamicTooltip(tooltip, 'top', true)}
	style = "${`${icon[2] ? `background-image: url(${icon[2]});` : ''}background-position:${
    -icon[0] * 48
  }px ${-icon[1] * 48}px`};">
	</div>`;
}

;// ./src/Cache/Stats/MissingUpgrades.js



/**
 * This functions caches variables related to missing upgrades
 * It is called by CM.Main.Loop() and CM.Cache.InitCache()
 * @global	{string}	CM.Cache.MissingUpgrades			String containig the HTML to create the "crates" for missing normal upgrades
 * @global	{string}	CM.Cache.MissingUpgradesCookies		String containig the HTML to create the "crates" for missing cookie upgrades
 * @global	{string}	CM.Cache.MissingUpgradesPrestige	String containig the HTML to create the "crates" for missing prestige upgrades
 */
function CacheAllMissingUpgrades() {
  CacheMissingUpgrades = '';
  CacheMissingUpgradesCookies = '';
  CacheMissingUpgradesPrestige = '';
  const list = [];
  // sort the upgrades
  Object.keys(Game.Upgrades).forEach((i) => {
    list.push(Game.Upgrades[i]);
  });
  const sortMap = function (a, b) {
    if (a.order > b.order) return 1;
    if (a.order < b.order) return -1;
    return 0;
  };
  list.sort(sortMap);

  Object.keys(list).forEach((i) => {
    const me = list[i];

    if (me.bought === 0) {
      let str = '';

      str += crateMissing(me);
      if (me.pool === 'prestige') CacheMissingUpgradesPrestige += str;
      else if (me.pool === 'cookie') CacheMissingUpgradesCookies += str;
      else if (me.pool !== 'toggle' && me.pool !== 'unused' && me.pool !== 'debug')
        CacheMissingUpgrades += str;
    }
  });
}

;// ./src/Cache/Stats/Reindeer.js



/**
 * This functions caches the reward of popping a reindeer
 * It is called by CM.Main.Loop() and CM.Cache.InitCache()
 * @global	{number}	CM.Cache.SeaSpec	The reward for popping a reindeer
 */
function CacheSeasonSpec() {
  if (Game.season === 'christmas') {
    let val = Game.cookiesPs * 60;
    if (Game.hasBuff('Elder frenzy')) val *= 0.5;
    if (Game.hasBuff('Frenzy')) val *= 0.75;
    CacheSeaSpec = Math.max(25, val);
    if (Game.Has('Ho ho ho-flavored frosting')) CacheSeaSpec *= 2;
  }

  FillCMDCache({ CacheSeaSpec: CacheSeaSpec });
}

;// ./src/Cache/Stats/Stats.js
/** Functions related to Caching stats */






/**
 * This functions caches variables related to the stats page
 */
function CacheStatsCookies() {
  CacheLucky = (CacheNoGoldSwitchCookiesPS * 900) / 0.15;
  CacheLucky *= CacheDragonsFortuneMultAdjustment;
  const cpsBuffMult = GetCPSBuffMult();
  if (cpsBuffMult > 0) CacheLucky /= cpsBuffMult;
  else CacheLucky = 0;
  CacheLuckyReward = CacheGoldenCookiesMult * (CacheLucky * 0.15) + 13;
  CacheLuckyWrathReward = CacheWrathCookiesMult * (CacheLucky * 0.15) + 13;
  CacheLuckyFrenzy = CacheLucky * 7;
  CacheLuckyRewardFrenzy = CacheGoldenCookiesMult * (CacheLuckyFrenzy * 0.15) + 13;
  CacheLuckyWrathRewardFrenzy = CacheWrathCookiesMult * (CacheLuckyFrenzy * 0.15) + 13;
  CacheConjure = CacheLucky * 2;
  CacheConjureReward = CacheConjure * 0.15;

  CacheEdifice = 0;
  let max = 0;
  let n = 0;
  Object.keys(Game.Objects).forEach((i) => {
    if (Game.Objects[i].amount > max) max = Game.Objects[i].amount;
    if (Game.Objects[i].amount > 0) n += 1;
  });
  Object.keys(Game.Objects).forEach((i) => {
    if (
      (Game.Objects[i].amount < max || n === 1) &&
      Game.Objects[i].amount < 400 &&
      Game.Objects[i].price * 2 > CacheEdifice
    ) {
      CacheEdifice = Game.Objects[i].price * 2;
      CacheEdificeBuilding = i;
    }
  });

  FillCMDCache({
    CacheLucky: CacheLucky,
    CacheLuckyReward: CacheLuckyReward,
    CacheLuckyWrathReward: CacheLuckyWrathReward,
    CacheLuckyFrenzy: CacheLuckyFrenzy,
    CacheLuckyRewardFrenzy: CacheLuckyRewardFrenzy,
    CacheLuckyWrathRewardFrenzy: CacheLuckyWrathRewardFrenzy,
    CacheConjure: CacheConjure,
    CacheConjureReward: CacheConjureReward,
    CacheEdifice: CacheEdifice,
    CacheEdificeBuilding: CacheEdificeBuilding,
  });
}

/**
 * This functions calculates the multipliers of Golden and Wrath cookie rewards
 */
function CacheGoldenAndWrathCookiesMults() {
  let goldenMult = 1;
  let wrathMult = 1;
  let mult = 1;

  // Factor auras and upgrade in mults
  if (SimHas('Green yeast digestives')) mult *= 1.01;
  if (SimHas('Dragon fang')) mult *= 1.03;

  goldenMult *= 1 + Game.auraMult('Ancestral Metamorphosis') * 0.1;
  goldenMult *= Game.eff('goldenCookieGain');
  wrathMult *= 1 + Game.auraMult('Unholy Dominion') * 0.1;
  wrathMult *= Game.eff('wrathCookieGain');

  // Calculate final golden and wrath multipliers
  CacheGoldenCookiesMult = mult * goldenMult;
  CacheWrathCookiesMult = mult * wrathMult;

  // Calculate Dragon's Fortune multiplier adjustment:
  // If Dragon's Fortune (or Reality Bending) aura is active and there are currently no golden cookies,
  // compute a multiplier adjustment to apply on the current CPS to simulate 1 golden cookie on screen.
  // Otherwise, the aura effect will be factored in the base CPS making the multiplier not requiring adjustment.
  CacheDragonsFortuneMultAdjustment = 1;
  if (Game.shimmerTypes.golden.n === 0) {
    CacheDragonsFortuneMultAdjustment *= 1 + Game.auraMult("Dragon's Fortune") * 1.23;
  }

  FillCMDCache({
    CacheGoldenCookiesMult: CacheGoldenCookiesMult,
    CacheWrathCookiesMult: CacheWrathCookiesMult,
    CacheDragonsFortuneMultAdjustment: CacheDragonsFortuneMultAdjustment,
  });
}

;// ./src/Cache/TillNextAchievement/IndividualAmountTillNextAchievement.js



function IndividualAmountTillNextAchievement(building) {
  const AchievementsAtStart = Game.AchievementsOwned;
  let index = 100;
  let lastIndexWithChange = 100;
  while (index > -1) {
    BuyBuildingsBonusIncome(building, index);
    if (SimAchievementsOwned > AchievementsAtStart) {
      lastIndexWithChange = index;
      index -= 10;
    } else if (index === 100) {
      return 101;
    } else {
      index += 1;
      while (index <= lastIndexWithChange) {
        BuyBuildingsBonusIncome(building, index);
        if (SimAchievementsOwned > AchievementsAtStart) {
          return index;
        }
        index += 1;
      }
    }
  }
  return 101;
}

;// ./src/Cache/TillNextAchievement/AllAmountTillNextAchievement.js





/**
 * This functions caches the amount of buildings needed till next achievement
 * @param	{boolean}	forceRecalc	Whether a recalcution should be forced (after CPS change)
 */
function AllAmountTillNextAchievement(forceRecalc) {
  const result = {};

  Object.keys(Game.Objects).forEach((i) => {
    if (
      Object.keys(CacheObjectsNextAchievement).length !== 0 &&
      CacheObjectsNextAchievement[i].TotalNeeded > Game.Objects[i].amount &&
      !forceRecalc
    ) {
      result[i] = {
        AmountNeeded: CacheObjectsNextAchievement[i].TotalNeeded - Game.Objects[i].amount,
        TotalNeeded: CacheObjectsNextAchievement[i].TotalNeeded,
        price: BuildingGetPrice(
          i,
          Game.Objects[i].basePrice,
          Game.Objects[i].amount,
          Game.Objects[i].free,
          CacheObjectsNextAchievement[i].TotalNeeded - Game.Objects[i].amount,
        ),
      };
    } else {
      const tillNext = IndividualAmountTillNextAchievement(i);
      result[i] = {
        AmountNeeded: tillNext,
        TotalNeeded: Game.Objects[i].amount + tillNext,
        price: BuildingGetPrice(
          i,
          Game.Objects[i].basePrice,
          Game.Objects[i].amount,
          Game.Objects[i].free,
          tillNext,
        ),
      };
    }
  });
  CacheObjectsNextAchievement = result;

  FillCMDCache({ CacheObjectsNextAchievement: CacheObjectsNextAchievement });
}

;// ./src/Cache/Wrinklers/Wrinklers.js
/** Caches data related to Wrinklers */





/**
 * This functions caches data related to Wrinklers
 * It is called by CM.Cache.LoopCache() and CM.Cache.InitCache()
 * @global	{number}				CM.Cache.WrinklersTotal		The cookies of all wrinklers
 * @global	{number}				CM.Cache.WrinklersNormal	The cookies of all normal wrinklers
 * @global	{[{number}, {number}]}	CM.Cache.WrinklersFattest	A list containing the cookies and the id of the fattest non-shiny wrinkler
 */
function CacheWrinklers() {
  CacheWrinklersTotal = 0;
  CacheWrinklersNormal = 0;
  CacheWrinklersFattest = [0, null];
  for (let i = 0; i < Game.wrinklers.length; i++) {
    let { sucked } = Game.wrinklers[i];
    let toSuck = 1.1;
    if (Game.Has('Sacrilegious corruption')) toSuck *= 1.05;
    if (Game.wrinklers[i].type === 1) toSuck *= 3; // Shiny wrinklers
    sucked *= toSuck;
    if (Game.Has('Wrinklerspawn')) sucked *= 1.05;
    if (SimObjects.Temple.minigameLoaded) {
      const godLvl = Game.hasGod('scorn');
      if (godLvl === 1) sucked *= 1.15;
      else if (godLvl === 2) sucked *= 1.1;
      else if (godLvl === 3) sucked *= 1.05;
    }
    CacheWrinklersTotal += sucked;
    if (Game.wrinklers[i].type === 0) {
      CacheWrinklersNormal += sucked;
      if (sucked > CacheWrinklersFattest[0]) CacheWrinklersFattest = [sucked, i];
    }
  }

  FillCMDCache({ CacheWrinklersTotal: CacheWrinklersTotal, CacheWrinklersNormal: CacheWrinklersNormal, CacheWrinklersFattest: CacheWrinklersFattest });
}

;// ./src/Cache/CacheInit.js













 // eslint-disable-line no-unused-vars


 // eslint-disable-line no-unused-vars

/**
 * This functions runs all cache-functions to generate all "full" cache
 */
function InitCache() {
  CacheDragonAuras();
  CacheWrinklers();
  // The "Lucky!" values are based on CpS without the golden switch, so it has to come first
  CacheNoGoldSwitchCPS();
  CacheStatsCookies();
  CacheGoldenAndWrathCookiesMults();
  CacheChain();
  CacheAllMissingUpgrades();
  CacheSeasonSpec();
  InitCookiesDiff();
  CacheAverageCookiesFromClicks = new CMAvgQueue(ClickTimes[ClickTimes.length - 1] * 20);
  CacheHeavenlyChipsPS();
  AllAmountTillNextAchievement();
  CacheAvgCPS();
  CacheIncome();
  CacheBuildingsPrices();
  PP_CachePP();
  CacheAscension(true);
  // Have the main loop recompute everything once before autoplay acts on these values
  SimDoSims = 1;
}

;// ./src/Disp/BuildingsUpgrades/UpgradeBar.js


/**
 * This function creates the legend for the upgrade bar
 * @returns	{object}	legend	The legend-object to be added
 */
function CreateUpgradeBarLegend() {
  const legend = document.createElement('div');
  legend.style.minWidth = '330px';
  legend.style.marginBottom = '4px';
  const title = document.createElement('div');
  title.className = 'name';
  title.style.marginBottom = '4px';
  title.textContent = 'Legend';
  legend.appendChild(title);

  const legendLine = function (colour, text) {
    const div = document.createElement('div');
    div.style.verticalAlign = 'middle';
    const span = document.createElement('span');
    span.className = ColourBackPre + colour;
    span.style.display = 'inline-block';
    span.style.height = '10px';
    span.style.width = '10px';
    span.style.marginRight = '4px';
    div.appendChild(span);
    div.appendChild(document.createTextNode(text));
    return div;
  };

  legend.appendChild(legendLine(ColourBlue, 'Better than the best PP of a building option'));
  legend.appendChild(legendLine(ColourGreen, 'Same as the best PP building option'));
  legend.appendChild(legendLine(ColourYellow, 'Within the top 10 of PP for buildings'));
  legend.appendChild(legendLine(ColourOrange, 'Within the top 20 of PP for buildings'));
  legend.appendChild(legendLine(ColourRed, 'Within the top 30 of PP for buildings'));
  legend.appendChild(legendLine(ColourPurple, 'Outside of the top 30 of PP for buildings'));
  legend.appendChild(legendLine(ColourGray, 'Negative or infinity PP'));
  return legend;
}

/**
 * This function creates the upgrade bar above the upgrade-section in the right section of the screen
 */
function CreateUpgradeBar() {
  const UpgradeBar = document.createElement('div');
  UpgradeBar.id = 'CMUpgradeBar';
  UpgradeBar.style.width = '100%';
  UpgradeBar.style.backgroundColor = 'black';
  UpgradeBar.style.textAlign = 'center';
  UpgradeBar.style.fontWeight = 'bold';
  UpgradeBar.style.display = 'none';
  UpgradeBar.style.zIndex = '21';
  UpgradeBar.onmouseout = function () {
    Game.tooltip.hide();
  };

  const placeholder = document.createElement('div');
  placeholder.appendChild(CreateUpgradeBarLegend());
  UpgradeBar.onmouseover = function () {
    Game.tooltip.draw(this, escape(placeholder.innerHTML), 'store');
  };

  const upgradeNumber = function (id, colour) {
    const span = document.createElement('span');
    span.id = id;
    span.className = ColourTextPre + colour;
    span.style.width = '14.28571428571429%';
    span.style.display = 'inline-block';
    span.textContent = '0';
    return span;
  };
  UpgradeBar.appendChild(upgradeNumber('CMUpgradeBarBlue', ColourBlue));
  UpgradeBar.appendChild(upgradeNumber('CMUpgradeBarGreen', ColourGreen));
  UpgradeBar.appendChild(upgradeNumber('CMUpgradeBarYellow', ColourYellow));
  UpgradeBar.appendChild(upgradeNumber('CMUpgradeBarOrange', ColourOrange));
  UpgradeBar.appendChild(upgradeNumber('CMUpgradeBarRed', ColourRed));
  UpgradeBar.appendChild(upgradeNumber('CMUpgradeBarPurple', ColourPurple));
  UpgradeBar.appendChild(upgradeNumber('CMUpgradeBarGray', ColourGray));

  l('upgrades').parentNode.insertBefore(UpgradeBar, l('upgrades').parentNode.childNodes[3]);
}

;// ./src/Disp/Initialization/CreateSectionHideButtons.js
/**
 * This function creates two objects at the top of the right column that allowing hiding the upgrade and building section
 */
function CreateSectionHideButtons() {
  const div = document.createElement('div');
  div.id = 'CMSectionHidButtons';
  div.style.textAlign = 'center';
  const a = document.createElement('a');
  a.className = 'option';
  a.onclick = function () {
    if (l('upgrades').style.display === 'flex') {
      l('upgrades').style.display = 'none';
      l('toggleUpgrades').style.display = 'none';
      l('techUpgrades').style.display = 'none';
      l('vaultUpgrades').style.display = 'none';
    } else {
      l('upgrades').style.display = 'flex';
      if (l('toggleUpgrades').children.length !== 0) l('toggleUpgrades').style.display = 'block';
      if (l('techUpgrades').children.length !== 0) l('techUpgrades').style.display = 'block';
      if (l('vaultUpgrades').children.length !== 0) l('vaultUpgrades').style.display = 'block';
    }
  };
  a.textContent = 'Hide/Show Upgrades';
  div.appendChild(a);
  const b = document.createElement('a');
  b.className = 'option';
  b.onclick = function () {
    if (l('products').style.display === 'grid') l('products').style.display = 'none';
    else l('products').style.display = 'grid';
  };
  b.textContent = 'Hide/Show Buildings';
  div.appendChild(b);
  l('store').insertBefore(div, l('store').childNodes[2]);
}

;// ./src/Disp/HelperFunctions/PopWrinklers.js
/**
 * This function pops all normal wrinklers
 * It is called by a click of the 'pop all' button created by CM.Disp.AddMenuStats()
 */
function PopAllNormalWrinklers() {
  Object.keys(Game.wrinklers).forEach((i) => {
    if (Game.wrinklers[i].sucked > 0 && Game.wrinklers[i].type === 0) {
      Game.wrinklers[i].hp = 0;
    }
  });
}

;// ./src/Disp/Tooltips/Tooltip.js

 // eslint-disable-line no-unused-vars





/** All general functions related to creating and updating tooltips */

/**
 * This function creates some very basic tooltips, (e.g., the tooltips in the stats page)
 * The tooltips are created with CM.Disp[placeholder].appendChild(desc)
 * @param	{string}	placeholder	The name used to later refer and spawn the tooltip
 * @param	{string}	text		The text of the tooltip
 * @param	{string}	minWidth	The minimum width of the tooltip
 */
function CreateSimpleTooltip(placeholder, text, minWidth) {
  const Tooltip = document.createElement('div');
  Tooltip.id = placeholder;
  const desc = document.createElement('div');
  desc.style.minWidth = minWidth;
  desc.style.marginBottom = '4px';
  const div = document.createElement('div');
  div.style.textAlign = 'left';
  div.textContent = text;
  desc.appendChild(div);
  Tooltip.appendChild(desc);
  SimpleTooltipElements[placeholder] = Tooltip;
}

/**
 * This function enhance the standard tooltips by creating and changing l('tooltip')
 * The function is called by .onmouseover events that have replaced original code to use CM.Disp.Tooltip()
 * @param	{string}	type					Type of tooltip (b, u, s or g)
 * @param	{string}	name					Name of the object/item the tooltip relates to
 * @returns {string}	l('tooltip').innerHTML	The HTML of the l('tooltip')-object
 */
function CreateTooltip(type, name) {
  if (type === 'b') {
    // Buildings
    l('tooltip').innerHTML = Game.Objects[name].tooltip();
    // Adds amortization info to the list of info per building
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipAmor === 1) {
      const buildPrice = BuildingGetPrice(
        name,
        Game.Objects[name].basePrice,
        0,
        Game.Objects[name].free,
        Game.Objects[name].amount,
      );
      const amortizeAmount = buildPrice - Game.Objects[name].totalCookies;
      if (amortizeAmount > 0) {
        l('tooltip').innerHTML = l('tooltip')
          .innerHTML.split('so far</div>')
          .join(
            `so far<br/>&bull; <b>${Beautify_Beautify(amortizeAmount)}</b> ${
              Math.floor(amortizeAmount) === 1 ? 'cookie' : 'cookies'
            } left to amortize (${
              GetTimeColour(
                (buildPrice - Game.Objects[name].totalCookies) /
                  (Game.Objects[name].storedTotalCps * Game.globalCpsMult),
              ).text
            })</div>`,
          );
      }
    }
    if (Game.buyMode === -1) {
      /*
       * Fix sell price displayed in the object tooltip.
       *
       * The buildings sell price displayed by the game itself (without any mod) is incorrect.
       * The following line of code fixes this issue, and can be safely removed when the game gets fixed.
       *
       * This issue is extensively detailed here: https://github.com/Aktanusa/CookieMonster/issues/359#issuecomment-735658262
       */
      l('tooltip').innerHTML = l('tooltip')
        .innerHTML.split(Beautify_Beautify(Game.Objects[name].bulkPrice))
        .join(
          Beautify_Beautify(
            BuildingSell(
              Game.Objects[name],
              Game.Objects[name].basePrice,
              Game.Objects[name].amount,
              Game.Objects[name].free,
              Game.buyBulk,
              1,
            ),
          ),
        );
    }
  } else if (type === 'u') {
    // Upgrades
    if (!Game.UpgradesInStore[name]) return '';
    l('tooltip').innerHTML = Game.crateTooltip(Game.UpgradesInStore[name], 'store');
  } else if (type === 's') l('tooltip').innerHTML = Game.lumpTooltip();
  // Sugar Lumps
  else if (type === 'g')
    l('tooltip').innerHTML = Game.Objects['Wizard tower'].minigame.spellTooltip(name)();
  // Grimoire
  else if (type === 'p')
    l('tooltip').innerHTML = Game.ObjectsById[2].minigame.tileTooltip(name[0], name[1])();
  // Harvest all button in garden
  else if (type === 'ha') l('tooltip').innerHTML = Game.ObjectsById[2].minigame.toolTooltip(1)();
  // Stock market
  else if (type === 'sm') l('tooltip').innerHTML = Game.Objects.Bank.minigame.goodTooltip(name)();
  else if (type === 'wb') l('tooltip').innerHTML = '';
  else if (type === 'pag') l('tooltip').innerHTML = Game.Objects.Temple.minigame.godTooltip(name)();
  else if (type === 'pas')
    l('tooltip').innerHTML = Game.Objects.Temple.minigame.slotTooltip(name[0])();

  // Adds area for extra tooltip-sections
  if (
    (type === 'b' && Game.buyMode === 1) ||
    type === 'u' ||
    type === 's' ||
    type === 'g' ||
    (type === 'p' && !Game.keys[16]) ||
    type === 'ha' ||
    type === 'sm' ||
    type === 'wb' ||
    type === 'pag' ||
    (type === 'pas' && name[1] !== -1)
  ) {
    const area = document.createElement('div');
    area.id = 'CMTooltipArea';
    l('tooltip').appendChild(area);
  }

  // Sets global variables used by CM.Disp.UpdateTooltip()
  TooltipType = type;
  TooltipName = name;

  UpdateTooltips();

  return l('tooltip').innerHTML;
}

;// ./src/Disp/Initialization/CreateWrinklerButton.js




/**
 * This function creates two objects at the bottom of the left column that allowing popping of wrinklers
 */
function CreateWrinklerButtons() {
  const popAllA = document.createElement('a');
  popAllA.id = 'PopAllNormalWrinklerButton';
  popAllA.textContent = 'Pop All Normal';
  popAllA.className = 'option';
  popAllA.onclick = function () {
    PopAllNormalWrinklers();
  };
  popAllA.onmouseout = function () {
    Game.tooltip.shouldHide = 1;
  };
  popAllA.onmouseover = function () {
    Game.tooltip.dynamic = 1;
    Game.tooltip.draw(this, () => CreateTooltip('wb', 'PopAllNormal'), 'this');
    Game.tooltip.wobble();
  };
  l('sectionLeftExtra').children[0].append(popAllA);
  const popFattestA = document.createElement('a');
  popFattestA.id = 'PopFattestWrinklerButton';
  popFattestA.textContent = 'Pop Single Fattest';
  popFattestA.className = 'option';
  popFattestA.onclick = function () {
    if (CacheWrinklersFattest[1] !== null) Game.wrinklers[CacheWrinklersFattest[1]].hp = 0;
  };
  popFattestA.onmouseout = function () {
    Game.tooltip.shouldHide = 1;
  };
  popFattestA.onmouseover = function () {
    Game.tooltip.dynamic = 1;
    Game.tooltip.draw(this, () => CreateTooltip('wb', 'PopFattest'), 'this');
    Game.tooltip.wobble();
  };
  l('sectionLeftExtra').children[0].append(popFattestA);
}

;// ./src/Disp/Initialization/CssArea.js


/** Static layout rules for the advisor, meters, compact tooltips and warnings */
const LayoutCSS = `
.CMAdvisor {
  margin: 4px 16px 10px;
  padding: 8px 10px;
  border: 1px solid rgba(255, 255, 255, 0.15);
  border-radius: 6px;
  background: rgba(0, 0, 0, 0.35);
}
.CMAdvisorHeadline { font-size: 15px; font-weight: bold; margin-bottom: 6px; }
.CMAdvisorGrid {
  display: grid;
  grid-template-columns: max-content 1fr;
  gap: 2px 12px;
  margin-top: 8px;
  font-size: 12px;
}
.CMAdvisorLabel { opacity: 0.65; }
.CMChecklist { margin: 8px 0 0 16px; padding: 0; font-size: 11px; opacity: 0.9; list-style: disc; }
.CMChecklist li { margin: 1px 0; }
.CMMeter {
  position: relative;
  height: 15px;
  border-radius: 8px;
  background: rgba(255, 255, 255, 0.08);
  box-shadow: inset 0 0 0 1px rgba(0, 0, 0, 0.6);
  overflow: hidden;
}
.CMMeterFill { position: absolute; left: 0; top: 0; bottom: 0; border-radius: 8px; transition: width 0.5s ease-out; }
.CMMeterLabel {
  position: absolute;
  inset: 0;
  font-size: 11px;
  line-height: 15px;
  font-weight: bold;
  text-align: center;
  color: #fff;
  text-shadow: 0 0 2px #000, 0 0 2px #000, 0 0 2px #000;
}
.CMHelpBubble {
  display: inline-block;
  width: 12px;
  height: 12px;
  border-radius: 6px;
  background: #c0c0c0;
  color: #000;
  font-size: 10px;
  line-height: 12px;
  text-align: center;
  vertical-align: middle;
  cursor: default;
}
.CMTooltipGrid {
  display: grid;
  grid-template-columns: max-content 1fr;
  gap: 1px 8px;
  align-items: baseline;
}
.CMTooltipGrid > .CMTooltipLabel { font-weight: bold; white-space: nowrap; }
.CMTooltipGrid > .CMTooltipValue { color: #fff; }
.CMTooltipNote { margin-top: 3px; font-size: 10px; opacity: 0.75; }
#CMDispTooltipWarningParent .CMWarnBox {
  padding: 3px 6px 4px;
  background: #000 url(img/darkNoise.png);
  border-radius: 3px;
}
#CMDispTooltipWarningParent .CMWarnTitle { font-weight: bold; margin-bottom: 2px; }
#CMDispTooltipWarningParent .CMWarnRow {
  display: flex;
  justify-content: space-between;
  gap: 10px;
  font-size: 11px;
  line-height: 14px;
}
#CMDispTooltipWarningParent .CMWarnRow > span:first-child { font-weight: bold; white-space: nowrap; }
#CMDispTooltipWarningParent .CMWarnRow > span:last-child { text-align: right; }
`;

/**
 * This function creates a CSS style that stores certain standard CSS classes used by CookieMonster
 * The colour classes are (re)written by UpdateColours(), the layout classes are static
 */
function CreateCssArea() {
  DispCSS = document.createElement('style');
  DispCSS.type = 'text/css';
  DispCSS.id = 'CMCSS';

  document.head.appendChild(DispCSS);

  const layout = document.createElement('style');
  layout.type = 'text/css';
  layout.id = 'CMLayoutCSS';
  layout.textContent = LayoutCSS;
  document.head.appendChild(layout);
}

;// ./src/Disp/Initialization/UpdateBuildingUpgradeStyle.js
/**
 * This function updates the style of the building and upgrade sections to make these sortable
 */
function UpdateBuildingUpgradeStyle() {
  l('products').style.display = 'grid';
  l('storeBulk').style.gridRow = '1/1';

  l('upgrades').style.display = 'flex';
  l('upgrades').style['flex-wrap'] = 'wrap';
}

;// ./src/Disp/TabTitle/FavIcon.js



/**
 * This function creates the Favicon, it is called by CM.Main.DelayInit()
 */
function CreateFavicon() {
  const Favicon = document.createElement('link');
  Favicon.id = 'CMFavicon';
  Favicon.rel = 'shortcut icon';
  Favicon.href = 'https://orteil.dashnet.org/cookieclicker/favicon.ico';
  document.getElementsByTagName('head')[0].appendChild(Favicon);
}

/**
 * This function updates the Favicon depending on whether a Golden Cookie has spawned
 * By relying on CM.Cache.spawnedGoldenShimmer it only changes for non-user spawned cookie
 */
function UpdateFavicon() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Favicon === 1 &&
    LastGoldenCookieState > 0
  ) {
    if (CacheSpawnedGoldenShimmer.wrath)
      l('CMFavicon').href =
        'https://CookieMonsterTeam.github.io/CookieMonster/favicon/wrathCookie.ico';
    else
      l('CMFavicon').href =
        'https://CookieMonsterTeam.github.io/CookieMonster/favicon/goldenCookie.ico';
  } else l('CMFavicon').href = 'https://orteil.dashnet.org/cookieclicker/favicon.ico';
}

;// ./src/Sim/InitializeData/InitData.js
/** Functions used to create static objects of Buildings, Upgrades and Achievements */







/**
 * This function creates static objects for Buildings, Upgrades and Achievements
 */
function InitData() {
  // Buildings
  SimObjects = [];
  Object.keys(Game.Objects).forEach((i) => {
    SimObjects[i] = InitialBuildingData(i);
  });

  // Upgrades
  SimUpgrades = [];
  Object.keys(Game.Upgrades).forEach((i) => {
    SimUpgrades[i] = InitUpgrade(i);
  });

  // Achievements
  SimAchievements = [];
  Object.keys(Game.Achievements).forEach((i) => {
    SimAchievements[i] = InitAchievement(i);
  });
  CopyData();
}

;// ./src/Main/ReplaceGameElements/TooltipGrimoire.js



/**
 * This function replaces the original .onmouseover functions of the Grimoire minigame
 */
function ReplaceTooltipGrimoire() {
  if (Game.Objects['Wizard tower'].minigameLoaded) {
    Object.keys(Game.Objects['Wizard tower'].minigame.spellsById).forEach((i) => {
      if (l(`grimoireSpell${i}`).onmouseover !== null) {
        TooltipGrimoireBackup[i] = l(`grimoireSpell${i}`).onmouseover;
        l(`grimoireSpell${i}`).onmouseover = function () {
          Game.tooltip.dynamic = 1;
          Game.tooltip.draw(this, () => CreateTooltip('g', `${i}`), 'this');
          Game.tooltip.wobble();
        };
      }
    });
  }
}

;// ./src/Main/ReplaceGameElements/NativeGrimoire.js





/**
 * This function fixes replaces the .draw function of the Grimoire
 */
function ReplaceNativeGrimoireDraw() {
  if (!HasReplaceNativeGrimoireDraw && Game.Objects['Wizard tower'].minigameLoaded) {
    const { minigame } = Game.Objects['Wizard tower'];
    BackupGrimoireDraw = minigame.draw;
    Game.Objects['Wizard tower'].minigame.draw = function () {
      BackupGrimoireDraw();
      if (
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GrimoireBar === 1 &&
        minigame.magic < minigame.magicM &&
        Game.drawT % 5 === 0
      ) {
        minigame.magicBarTextL.innerHTML += ` (${FormatTime(
          CalculateGrimoireRefillTime(minigame.magic, minigame.magicM, minigame.magicM),
        )})`;
        minigame.magicBarL.style.width = '75%'; // TODO: Fix this after Orteil pushes fix to main game;
      }
    };
    HasReplaceNativeGrimoireDraw = true;
  }
}

/**
 * This function fixes replaces the .launch function of the Grimoire
 */
function ReplaceNativeGrimoireLaunch() {
  if (!HasReplaceNativeGrimoireLaunch && Game.Objects['Wizard tower'].minigameLoaded) {
    const { minigame } = Game.Objects['Wizard tower'];
    BackupGrimoireLaunch = minigame.launch;
    BackupGrimoireLaunchMod = new Function( // eslint-disable-line no-new-func
      `return ${minigame.launch
        .toString()
        .split('=this')
        .join("= Game.Objects['Wizard tower'].minigame")}`,
    );
    Game.Objects['Wizard tower'].minigame.launch = function () {
      BackupGrimoireLaunchMod();
      ReplaceTooltipGrimoire();
      HasReplaceNativeGrimoireDraw = false;
      ReplaceNativeGrimoireDraw();

      HasReplaceNativeGrimoireLaunch = true;
    };
  }
}

/**
 * This function fixes replaces the Launch and Draw functions of the Grimoire
 */
function ReplaceNativeGrimoire() {
  ReplaceNativeGrimoireLaunch();
  ReplaceNativeGrimoireDraw();
}

;// ./src/Main/ReplaceGameElements/Tooltips.js
/** Functions related to replacing tooltips */



 // eslint-disable-line no-unused-vars



/**
 * This function replaces the original .onmouseover functions of buildings
 */
function ReplaceTooltipBuild() {
  Object.keys(Game.Objects).forEach((i) => {
    const me = Game.Objects[i];
    if (l(`product${me.id}`).onmouseover !== null) {
      TooltipBuildBackup[i] = l(`product${me.id}`).onmouseover;
      l(`product${me.id}`).onmouseover = function () {
        Game.tooltip.dynamic = 1;
        Game.tooltip.draw(this, () => CreateTooltip('b', `${i}`), 'store');
        Game.tooltip.wobble();
      };
    }
  });
}

/**
 * This function replaces the original .onmouseover functions of sugar lumps
 */
function ReplaceTooltipLump() {
  if (Game.canLumps()) {
    TooltipLumpBackup = l('lumps').onmouseover;
    l('lumps').onmouseover = function () {
      Game.tooltip.dynamic = 1;
      Game.tooltip.draw(this, () => CreateTooltip('s', 'Lump'), 'this');
      Game.tooltip.wobble();
    };
  }
}

/**
 * Replaces functions for the garden minigame
 */
function ReplaceTooltipGarden() {
  if (Game.Objects.Farm.minigameLoaded) {
    l('gardenTool-1').onmouseover = function () {
      Game.tooltip.dynamic = 1;
      Game.tooltip.draw(this, () => CreateTooltip('ha', 'HarvestAllButton'), 'this');
      Game.tooltip.wobble();
    };
    Array.from(l('gardenPlot').children).forEach((child) => {
      const coords = child.id.slice(-3);
      // eslint-disable-next-line no-param-reassign
      child.onmouseover = function () {
        Game.tooltip.dynamic = 1;
        Game.tooltip.draw(this, () => CreateTooltip('p', [`${coords[0]}`, `${coords[2]}`]), 'this');
        Game.tooltip.wobble();
      };
    });

    // overwrite the harvesting function to allow CachePlotChances to be updated
    const OldBuildPlot = Game.Objects.Farm.minigame.buildPlot;
    Game.Objects.Farm.minigame.buildPlot = function () {
      OldBuildPlot(arguments); // eslint-disable-line prefer-rest-params
      CalculateAllPlotChances(Game.Objects.Farm.minigame, Game.auraMult('Supreme Intellect'));
    };
  }
}

/**
 * This function replaces the original .onmouseover functions of all stocks
 */
function ReplaceTooltipMarket() {
  if (Game.Objects.Bank.minigameLoaded) {
    for (let i = 0; i < Game.Objects.Bank.minigame.goodsById.length; i++) {
      l(`bankGood-${i}`).firstChild.onmouseover = function () {
        Game.tooltip.dynamic = 1;
        Game.tooltip.draw(this, () => CreateTooltip('sm', i), 'this');
        Game.tooltip.wobble();
      };
    }
  }
}

function ReplaceTooltipPantheon() {
  if (Game.Objects.Temple.minigameLoaded) {
    for (let i = 0; i < 11; i += 1) {
      l(`templeGod${i}`).onmouseover = function () {
        Game.tooltip.dynamic = 1;
        Game.tooltip.draw(this, () => CreateTooltip('pag', i), 'this');
        Game.tooltip.wobble();
      };
    }
    for (let i = 0; i < 3; i += 1) {
      l(`templeSlot${i}`).onmouseover = function () {
        Game.tooltip.dynamic = 1;
        Game.tooltip.draw(
          this,
          () => CreateTooltip('pas', [i, Game.Objects.Temple.minigame.slot[i]]),
          'this',
        );
        Game.tooltip.wobble();
      };
    }
  }
}

/**
 * This function call all functions that replace Game-tooltips with Cookie Monster enhanced tooltips
 */
function ReplaceTooltips() {
  ReplaceTooltipBuild();
  ReplaceTooltipLump();

  // Replace Tooltips of Minigames. Nesting it in LoadMinigames makes sure to replace them even if
  // they were not loaded initially
  // eslint-disable-next-line prefer-destructuring
  LoadMinigames = Game.LoadMinigames;
  Game.LoadMinigames = function () {
    LoadMinigames();
    ReplaceTooltipGarden();
    ReplaceTooltipGrimoire();
    ReplaceTooltipMarket();
    ReplaceTooltipPantheon();
    ReplaceNativeGrimoire();
  };
  Game.LoadMinigames();
}

;// ./src/Cache/Dragon/Dragon.js
/** Functions related to the Dragon */





 // eslint-disable-line no-unused-vars

/**
 * This functions caches the current cost of upgrading the dragon level so it can be displayed in the tooltip
 */
function CacheDragonCost() {
  if (CacheLastDragonLevel !== Game.dragonLevel || SimDoSims) {
    if (
      Game.dragonLevel < 25 &&
      Game.dragonLevels[Game.dragonLevel].buy.toString().includes('sacrifice')
    ) {
      const objectMatch = Game.dragonLevels[Game.dragonLevel].buy
        .toString()
        .match(/Objects\[(.*)\]/);
      let target =
        objectMatch !== null ? objectMatch[1] : Game.ObjectsById[Game.dragonLevel - 5].name;
      const amount = Game.dragonLevels[Game.dragonLevel].buy
        .toString()
        .match(/sacrifice\((.*?)\)/)[1];
      if (target !== 'i') {
        target = target.replaceAll("'", '');
        if (Game.Objects[target].amount < amount) {
          CacheCostDragonUpgrade = 'Not enough buildings to sell';
        } else {
          let cost = 0;
          CopyData();
          for (let i = 0; i < amount; i++) {
            let price =
              SimObjects[target].basePrice *
              Game.priceIncrease **
                Math.max(0, SimObjects[target].amount - 1 - SimObjects[target].free);
            price = Game.modifyBuildingPrice(SimObjects[target], price);
            price = Math.ceil(price);
            cost += price;
            SimObjects[target].amount -= 1;
          }
          CacheCostDragonUpgrade = `Cost to rebuy: ${Beautify_Beautify(cost)}`;
        }
      } else {
        let cost = 0;
        CopyData();
        Object.keys(Game.Objects).forEach((j) => {
          target = j;
          if (Game.Objects[target].amount < amount) {
            CacheCostDragonUpgrade = 'Not enough buildings to sell';
            return;
          }
          for (let i = 0; i < amount; i++) {
            let price =
              SimObjects[target].basePrice *
              Game.priceIncrease **
                Math.max(0, SimObjects[target].amount - 1 - SimObjects[target].free);
            price = Game.modifyBuildingPrice(SimObjects[target], price);
            price = Math.ceil(price);
            cost += price;
            SimObjects[target].amount -= 1;
          }
          CacheCostDragonUpgrade = `Cost to rebuy: ${Beautify_Beautify(cost)}`;
        });
      }
    }
    CacheLastDragonLevel = Game.dragonLevel;
  }

  FillCMDCache({ CacheLastDragonLevel: CacheLastDragonLevel });
}

;// ./src/Sim/SimulationEvents/AuraChange.js






/**
 * This functions calculates the cps and cost of changing a Dragon Aura
 * It is called by CM.Disp.AddAuraInfo()
 * @param	{number}			aura										The number of the aura currently selected by the mouse/user
 * @returns {[number, number]} 	[CM.Sim.cookiesPs - Game.cookiesPs, price]	The bonus cps and the price of the change
 */
function CalculateChangeAura(aura) {
  CopyData();

  // Check if aura being changed is first or second aura
  const auraToBeChanged = l('promptContent').children[0].innerHTML.includes('secondary');
  if (auraToBeChanged) SimDragonAura2 = aura;
  else SimDragonAura = aura;

  // Sell highest building but only if aura is different
  let price = 0;
  if (SimDragonAura !== CacheDragonAura || SimDragonAura2 !== CacheDragonAura2) {
    for (let i = Game.ObjectsById.length - 1; i > -1; --i) {
      if (Game.ObjectsById[i].amount > 0) {
        const highestBuilding = SimObjects[Game.ObjectsById[i].name].name;
        SimObjects[highestBuilding].amount -= 1;
        SimBuildingsOwned -= 1;
        price =
          SimObjects[highestBuilding].basePrice *
          Game.priceIncrease **
            Math.max(0, SimObjects[highestBuilding].amount - 1 - SimObjects[highestBuilding].free);
        price = Game.modifyBuildingPrice(SimObjects[highestBuilding], price);
        price = Math.ceil(price);
        break;
      }
    }
  }

  const lastAchievementsOwned = SimAchievementsOwned;
  CalculateGains();

  CheckOtherAchiev();
  if (lastAchievementsOwned !== SimAchievementsOwned) {
    CalculateGains();
  }
  return [SimCookiesPs - Game.cookiesPs, price];
}

;// ./src/Disp/Dragon/Dragon.js
/** Functions related to the Dragon */







/**
 * This functions adds the two extra lines about CPS and time to recover to the aura picker infoscreen
 * @param	{number}	aura	The number of the aura currently selected by the mouse/user
 */
function AddAuraInfo(aura) {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.DragonAuraInfo === 1) {
    const [bonusCPS, priceOfChange] = CalculateChangeAura(aura);
    const timeToRecover = FormatTime(priceOfChange / (bonusCPS + Game.cookiesPs));
    let bonusCPSPercentage;
    if (Game.cookiesPs === 0) bonusCPSPercentage = Beautify_Beautify(Infinity);
    else bonusCPSPercentage = Beautify_Beautify((bonusCPS / Game.cookiesPs) * 100);

    l('dragonAuraInfo').style.minHeight = '120px';
    l('dragonAuraInfo').style.margin = '8px';
    l('dragonAuraInfo').appendChild(document.createElement('div')).className = 'line';
    const div = document.createElement('div');
    div.style.minWidth = '200px';
    div.style.textAlign = 'center';
    div.textContent = `Picking this aura will change CPS by ${Beautify_Beautify(
      bonusCPS,
    )} (${bonusCPSPercentage}% of current CPS).`;
    l('dragonAuraInfo').appendChild(div);
    const div2 = document.createElement('div');
    div2.style.minWidth = '200px';
    div2.style.textAlign = 'center';
    div2.textContent = `It will take ${timeToRecover} to recover the cost.`;
    l('dragonAuraInfo').appendChild(div2);
  }
}

/**
 * This functions adds a tooltip to the level up button displaying the cost of rebuying all
 * It is called by Game.ToggleSpecialMenu() after CM.Main.ReplaceNative()
 */
function AddDragonLevelUpTooltip() {
  // Check if it is the dragon popup that is on screen
  if (
    (l('specialPopup').className.match(/onScreen/) &&
      l('specialPopup').children[0].style.background.match(/dragon/)) !== null
  ) {
    for (let i = 0; i < l('specialPopup').childNodes.length; i++) {
      if (l('specialPopup').childNodes[i].className === 'optionBox') {
        l('specialPopup').children[i].onmouseover = function () {
          CacheDragonCost();
          Game.tooltip.dynamic = 1;
          Game.tooltip.draw(
            l('specialPopup'),
            `<div style="min-width:200px;text-align:center;">${CacheCostDragonUpgrade}</div>`,
            'this',
          );
          Game.tooltip.wobble();
        };
        l('specialPopup').children[i].onmouseout = function () {
          Game.tooltip.shouldHide = 1;
        };
      }
    }
  }
}

;// ./src/Data/Sectionheaders.js
/** Data related to the display titles of certain sections in menu screens */

/** Display titles of the headers of the Cookie Monster settings section */
const ConfigGroups = {
  Favourite: 'Favourite Settings',
  Calculation: 'Calculation',
  Notation: 'Notation',
  Colours: 'Colours and colour coding',
  BarsDisplay: 'Infobars and visual settings',
  Tooltip: 'Tooltips',
  Statistics: 'Statistics',
  Notification: 'Notifications',
  Autoplay: 'Autoplay',
  Miscellaneous: 'Miscellaneous',
};

/** Display titles of the headers of the notification section of the Cookie Monster settings */
const ConfigGroupsNotification = {
  NotificationGeneral: 'General Notifications',
  NotificationGC: 'Golden Cookie',
  NotificationFC: 'Fortune Cookie',
  NotificationSea: 'Season Special',
  NotificationGard: 'Garden Tick',
  NotificationMagi: 'Full Magic Bar',
  NotificationWrink: 'Wrinkler',
  NotificationWrinkMax: 'Maximum Wrinklers',
  NotificationAscend: 'Optimal Ascension',
};

;// ./src/Config/CheckNotificationPermissions.js
/**
 * This function checks if the user has given permissions for notifications
 * It is called by a change in any of the notification options
 * Note that most browsers will stop asking if the user has ignored the prompt around 6 times
 * @param 	{number}	ToggleOnOff		A number indicating whether the option has been turned off (0) or on (1)
 */
function CheckNotificationPermissions(ToggleOnOff) {
  if (ToggleOnOff === 1) {
    // Check if browser support Promise version of Notification Permissions
    const checkNotificationPromise = function () {
      try {
        Notification.requestPermission().then();
        // eslint-disable-next-line no-unused-vars
      } catch (e) {
        return false;
      }
      return true;
    };

    // Check if the browser supports notifications and which type
    if (!('Notification' in window)) {
      console.log('This browser does not support notifications.'); // eslint-disable-line no-console
    } else if (checkNotificationPromise()) {
      Notification.requestPermission().then();
    } else {
      Notification.requestPermission();
    }
  }
}

/* harmony default export */ const Config_CheckNotificationPermissions = (CheckNotificationPermissions);

;// ./src/Disp/HelperFunctions/RefreshScale.js




/**
 * This function refreshes all numbers after a change in scale-setting
 * It is therefore called by a changes in CM.Options.Scale, CM.Options.ScaleDecimals, CM.Options.ScaleSeparator and CM.Options.ScaleCutoff
 */
function RefreshScale() {
  BeautifyAll();
  Game.RefreshStore();
  Game.RebuildUpgrades();

  UpdateBotBar();
  UpdateBuildings();
  UpdateUpgrades();
}

;// ./src/Config/Toggles/ToggleBotBar.js



/**
 * This function toggle the bottom bar
 * It is called by CM.Disp.UpdateAscendState() and a change in Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar
 */
function ToggleBotBar() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar === 1) {
    l('CMBotBar').style.display = '';
    UpdateBotBar();
  } else {
    l('CMBotBar').style.display = 'none';
  }
  UpdateBotTimerBarPosition();
}

;// ./src/Config/Toggles/ToggleDetailedTime.js



/**
 * This function changes some of the time-displays in the game to be more detailed
 * It is called by a change in CM.Options.DetailedTime
 */
function ToggleDetailedTime() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.DetailedTime === 1)
    Game.sayTime = CMSayTime;
  else Game.sayTime = BackupFunctions.sayTime;
}

;// ./src/Config/Toggles/ToggleGCTimer.js



/**
 * This function toggles GC Timers are visible
 * It is called by a change in CM.Options.GCTimer
 */
function ToggleGCTimer() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GCTimer === 1) {
    Object.keys(GCTimers).forEach((i) => {
      GCTimers[i].style.display = 'block';
      GCTimers[i].style.left = CacheGoldenShimmersByID[i].l.style.left;
      GCTimers[i].style.top = CacheGoldenShimmersByID[i].l.style.top;
    });
  } else {
    // eslint-disable-next-line no-return-assign
    Object.keys(GCTimers).forEach((i) => (GCTimers[i].style.display = 'none'));
  }
}

;// ./src/Config/Toggles/ToggleSectionHideButtons.js
/**
 * This function updates the display setting of the two objects created by CM.Disp.CreateWrinklerButtons()
 * It is called by changes in CM.Options.WrinklerButtons
 */
function ToggleSectionHideButtons() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.HideSectionsButtons) {
    l('CMSectionHidButtons').style.display = '';
  } else {
    l('CMSectionHidButtons').style.display = 'none';
  }
}

;// ./src/Config/Toggles/ToggleUpgradeBarAndColour.js


/**
 * This function toggles the upgrade bar and the colours of upgrades
 * It is called by a change in CM.Options.UpBarColour
 */
function ToggleUpgradeBarAndColour() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.UpBarColour === 1) {
    // Colours and bar on
    l('CMUpgradeBar').style.display = '';
    UpdateUpgrades();
  } else if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.UpBarColour === 2
  ) {
    // Colours on and bar off
    l('CMUpgradeBar').style.display = 'none';
    UpdateUpgrades();
  } else {
    // Colours and bar off
    l('CMUpgradeBar').style.display = 'none';
    Game.RebuildUpgrades();
  }
}

;// ./src/Config/Toggles/ToggleUpgradeBarFixedPos.js
/**
 * This function toggles the position of the upgrade bar from fixed or non-fixed mode
 * It is called by a change in CM.Options.UpgradeBarFixedPos
 */
function ToggleUpgradeBarFixedPos() {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.UpgradeBarFixedPos === 1
  ) {
    // Fix to top of screen when scrolling
    l('CMUpgradeBar').style.position = 'sticky';
    l('CMUpgradeBar').style.top = '0px';
  } else {
    l('CMUpgradeBar').style.position = ''; // Possible to scroll offscreen
  }
}

;// ./src/Data/settings.js




 // eslint-disable-line no-unused-vars














/** This includes all options of CookieMonster and their relevant data */
const settings_settings = {
  // Calculation
  CPSMode: new settingClasses.SettingStandard(
    1,
    'bool',
    'Calculation',
    ['Current cookies per second', 'Average cookies per second'],
    'Calculate times using current cookies per second or average cookies per second',
    false,
  ),
  AvgCPSHist: new settingClasses.SettingStandard(
    3,
    'bool',
    'Calculation',
    [
      'Average CPS in past 10s',
      'Average CPS in past 15s',
      'Average CPS in past 30s',
      'Average CPS in past 1m',
      'Average CPS in past 5m',
      'Average CPS in past 10m',
      'Average CPS in past 15m',
      'Average CPS in past 30m',
    ],
    'How much time average Cookies Per Second should consider',
    false,
  ),
  AvgClicksHist: new settingClasses.SettingStandard(
    0,
    'bool',
    'Calculation',
    [
      'Average clicks in past 1s',
      'Average clicks in past 5s',
      'Average clicks in past 10s',
      'Average clicks in past 15s',
      'Average clicks in past 30s',
    ],
    'How much time average Cookie Clicks should consider',
    false,
  ),
  CalcWrink: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'Calculation',
    [
      'Calculate with wrinklers OFF',
      'Calculate with wrinklers ON',
      'Calculate with single fattest wrinkler ON',
    ],
    'Calculate times and average Cookies Per Second with (only the single non-shiny fattest) wrinklers',
    true,
    () => {
      SimDoSims = true;
    },
  ),
  AscendOverhead: new settingClasses.SettingInputNumber(
    60,
    'numscale',
    'Calculation',
    'Ascension overhead (seconds): ',
    'Time lost per ascension (ascending, spending heavenly chips, restarting) used by the ascension advisor. The optimal ascension time is not very sensitive to this value',
    0,
    Infinity,
  ),

  // Notation
  Scale: new settingClasses.SettingStandardWithFunc(
    2,
    'bool',
    'Notation',
    [
      "Game's setting scale",
      'Metric',
      'Short scale',
      'Short scale (Abbreviated)',
      'Scientific notation',
      'Engineering notation',
    ],
    'Change how long numbers are formatted',
    false,
    () => {
      RefreshScale();
    },
  ),
  ScaleDecimals: new settingClasses.SettingStandardWithFunc(
    2,
    'bool',
    'Notation',
    ['1 decimals', '2 decimals', '3 decimals'],
    `Set the number of decimals used when applicable. This only works with Cookie Monster scales and not with "Game's Setting Scale"`,
    false,
    () => {
      RefreshScale();
    },
  ),
  ScaleSeparator: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'Notation',
    ['. for decimals (standard)', '. for thousands'],
    'Set the separator used for decimals and thousands',
    false,
    () => {
      RefreshScale();
    },
  ),
  ScaleCutoff: new settingClasses.SettingInputNumber(
    999999,
    'numscale',
    'Notation',
    'Notation cut-off point: ',
    'The number from which Cookie Monster will start formatting numbers based on chosen scale. Standard is 999,999. Setting this above 999,999,999 might break certain notations',
    1,
    999999999,
  ),
  TimeFormat: new settingClasses.SettingStandard(
    0,
    'bool',
    'Notation',
    ['Time XXd, XXh, XXm, XXs', 'Time XX:XX:XX:XX:XX', 'Time XXx, XXx'],
    'Change the time format',
    false,
  ),
  DetailedTime: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'Notation',
    ['Detailed time OFF', 'Detailed time ON'],
    'Change how time is displayed in certain statistics and tooltips',
    true,
    () => {
      ToggleDetailedTime();
    },
  ),
  PPDisplayTime: new settingClasses.SettingStandard(
    0,
    'bool',
    'Notation',
    ['PP as value (standard)', 'PP as time unit'],
    'Display PP as calculated value or as approximate time unit. Note that PP does not translate directly into a time unit and this is therefore only an approximation.',
    false,
  ),

  // Colours
  BuildColour: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'Colours',
    ['Building colours OFF', 'Building colours ON'],
    'Colour code buildings',
    true,
    () => {
      UpdateBuildings();
    },
  ),
  PPOnlyConsiderBuyable: new settingClasses.SettingStandard(
    0,
    'bool',
    'Colours',
    ["Don't ignore non-buyable", 'Ignore non-buyable'],
    "Makes Cookie Monster label buildings and upgrades you can't buy right now red, useful in those situations where you just want to spend your full bank 'most optimally'",
    true,
  ),
  PPExcludeTop: new settingClasses.SettingStandard(
    0,
    'bool',
    'Colours',
    [
      "Don't ignore any",
      'Ignore 1st best',
      'Ignore 1st and 2nd best',
      'Ignore 1st, 2nd and 3rd best',
    ],
    'Makes Cookie Monster ignore the 1st, 2nd or 3rd best buildings in labeling and colouring PP values',
    true,
  ),
  PPRigidelMode: new settingClasses.SettingStandard(
    0,
    'bool',
    'Colours',
    ['Rigidel mode OFF', 'Rigidel mode ON'],
    'Makes Cookie Monster ignore all "buy 1" options when colouring PP in order to stay at a total building count ending in 10 for pantheon god Rigidel',
    true,
  ),
  PPSecondsLowerLimit: new settingClasses.SettingInputNumber(
    0,
    'numscale',
    'Colours',
    'Lower limit for PP (in seconds): ',
    'If a building or upgrade costs less than the specified seconds of CPS it will also be considered optimal and label it as such ("PP is less than xx seconds of CPS"); setting to 0 ignores this option',
    0,
    Infinity,
  ),
  ColourBlue: new settingClasses.SettingColours(
    '#4bb8f0',
    'colour',
    'Colours',
    'Standard colour is blue. Used to show upgrades better than best PP building, for Click Frenzy bar, and for various labels',
  ),
  ColourGreen: new settingClasses.SettingColours(
    '#00ff00',
    'colour',
    'Colours',
    'Standard colour is green. Used to show best PP building, for Blood Frenzy bar, and for various labels',
  ),
  ColourYellow: new settingClasses.SettingColours(
    '#ffff00',
    'colour',
    'Colours',
    'Standard colour is yellow. Used to show buildings within the top 10 of PP, for Frenzy bar, and for various labels',
  ),
  ColourOrange: new settingClasses.SettingColours(
    '#ff7f00',
    'colour',
    'Colours',
    'Standard colour is orange. Used to show buildings within the top 20 of PP, for Next Reindeer bar, and for various labels',
  ),
  ColourRed: new settingClasses.SettingColours(
    '#ff0000',
    'colour',
    'Colours',
    'Standard colour is Red. Used to show buildings within the top 30 of PP, for Clot bar, and for various labels',
  ),
  ColourPurple: new settingClasses.SettingColours(
    '#ff00ff',
    'colour',
    'Colours',
    'Standard colour is purple. Used to show buildings outside of the top 30 of PP, for Next Cookie bar, and for various labels',
  ),
  ColourGray: new settingClasses.SettingColours(
    '#b3b3b3',
    'colour',
    'Colours',
    'Standard colour is gray. Used to show negative or infinity PP, and for Next Cookie/Next Reindeer bar',
  ),
  ColourPink: new settingClasses.SettingColours(
    '#ff1493',
    'colour',
    'Colours',
    'Standard colour is pink. Used for Dragonflight bar',
  ),
  ColourBrown: new settingClasses.SettingColours(
    '#8b4513',
    'colour',
    'Colours',
    'Standard colour is brown. Used for Dragon Harvest bar',
  ),

  // BarsDisplay
  BotBar: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'BarsDisplay',
    ['Bottom bar OFF', 'Bottom bar ON'],
    'Building information',
    true,
    () => {
      ToggleBotBar();
    },
  ),
  TimerBar: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'BarsDisplay',
    ['Timer bar OFF', 'Timer bar ON'],
    'Bar with timers for golden cookie, season popup, Frenzy (Normal, Clot, Elder), Click Frenzy',
    true,
    () => {
      ToggleTimerBar();
    },
  ),
  TimerBarPos: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'BarsDisplay',
    ['Timer bar position (top left)', 'Timer bar position (bottom)'],
    'Placement of the timer bar',
    false,
    () => {
      ToggleTimerBarPos();
    },
  ),
  TimerBarOverlay: new settingClasses.SettingStandard(
    2,
    'bool',
    'BarsDisplay',
    ['Timer bar overlay OFF', 'Timer bar overlay only seconds', 'Timer bar overlay full'],
    'Overlay on timers displaying seconds and/or percentage left',
    true,
  ),
  AutosaveTimerBar: new settingClasses.SettingStandard(
    0,
    'bool',
    'BarsDisplay',
    ['Autosave timer bar OFF', 'Autosave timer bar ON'],
    'Show a timer counting down till next autosave in the timer bar',
    true,
  ),
  AscendTimerBar: new settingClasses.SettingStandard(
    1,
    'bool',
    'BarsDisplay',
    ['Ascension readiness bar OFF', 'Ascension readiness bar ON'],
    'Show how close the run is to the optimal ascension time in the timer bar',
    true,
  ),
  UpBarColour: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'BarsDisplay',
    ['Upgrade colours/bar OFF', 'Upgrade colours with bar ON', 'Upgrade colours without bar ON'],
    'Colour code upgrades and optionally add a counter bar',
    false,
    () => {
      ToggleUpgradeBarAndColour();
    },
  ),
  UpgradeBarFixedPos: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'BarsDisplay',
    ['Upgrade bar fixed position OFF', 'Upgrade bar fixed position ON'],
    'Lock the upgrade bar at top of the screen to prevent it from moving ofscreen when scrolling',
    true,
    () => {
      ToggleUpgradeBarFixedPos();
    },
  ),
  SortBuildings: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'BarsDisplay',
    [
      'Sort buildings: default',
      'Sort buildings: PP of x1 purchase',
      'Sort buildings: PP of selected bulk mode',
      'Sort buildings: price until next achievement',
    ],
    'Sort the display of buildings in default order, by PP, or until next achievement',
    false,
    () => {
      UpdateBuildings();
    },
  ),
  SortUpgrades: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'BarsDisplay',
    ['Sort upgrades: default', 'Sort upgrades: PP'],
    'Sort the display of upgrades in either default order or by PP',
    false,
    () => {
      UpdateUpgrades();
    },
  ),
  UpgradesNeverCollapse: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'BarsDisplay',
    ['Upgrades always expanded OFF', 'Upgrades always expanded ON'],
    'Toggle to make the upgrades sections always expanded to the size needed to display all upgrades',
    true,
    () => {
      UpdateUpgradeSectionsHeight();
    },
  ),
  DragonAuraInfo: new settingClasses.SettingStandard(
    1,
    'bool',
    'BarsDisplay',
    ['Extra dragon aura info OFF', 'Extra dragon aura info ON'],
    'Shows information about changes in CPS and costs in the dragon aura interface.',
    true,
  ),
  GrimoireBar: new settingClasses.SettingStandard(
    1,
    'bool',
    'BarsDisplay',
    ['Grimoire magic meter timer OFF', 'Grimoire magic meter timer ON'],
    'A timer overlay showing how long till the Grimoire magic meter is full',
    true,
  ),
  GCTimer: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'BarsDisplay',
    ['Golden cookie timer OFF', 'Golden cookie timer ON'],
    'A timer on the golden cookie when it has been spawned',
    true,
    () => {
      ToggleGCTimer();
    },
  ),
  Favicon: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'BarsDisplay',
    ['Favicon OFF', 'Favicon ON'],
    'Update favicon with golden/wrath cookie',
    true,
    () => {
      UpdateFavicon();
    },
  ),
  WrinklerButtons: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'BarsDisplay',
    ['Extra wrinkler buttons OFF', 'Extra wrinkler buttons ON'],
    'Show buttons for popping wrinklers at bottom of cookie section',
    true,
    () => {
      ToggleWrinklerButtons();
    },
  ),
  HideSectionsButtons: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'BarsDisplay',
    ['Hide buildings/upgrades button OFF', 'Hide buildings/upgrades button ON'],
    'Show buttons for hiding and showing the buildings and upgrades sections in the right column',
    true,
    () => {
      ToggleSectionHideButtons();
    },
  ),

  // Tooltip
  TooltipBuildUpgrade: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Building/upgrade tooltip information OFF', 'Building/upgrade tooltip information ON'],
    'Extra information in building/upgrade tooltips',
    true,
  ),
  TooltipAmor: new settingClasses.SettingStandard(
    0,
    'bool',
    'Tooltip',
    [
      'Buildings tooltip amortization information OFF',
      'Buildings tooltip amortization information ON',
    ],
    'Add amortization information to buildings tooltip',
    true,
  ),
  ToolWarnLucky: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Tooltip lucky warning OFF', 'Tooltip lucky warning ON'],
    'A warning when buying if it will put the bank under the amount needed for max "Lucky!" rewards',
    true,
  ),
  ToolWarnLuckyFrenzy: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Tooltip lucky frenzy warning OFF', 'Tooltip lucky frenzy warning ON'],
    'A warning when buying if it will put the bank under the amount needed for max "Lucky!" (Frenzy) rewards',
    true,
  ),
  ToolWarnConjure: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Tooltip conjure warning OFF', 'Tooltip conjure warning ON'],
    'A warning when buying if it will put the bank under the amount needed for max "Conjure Baked Goods" rewards',
    true,
  ),
  ToolWarnConjureFrenzy: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Tooltip conjure frenzy warning OFF', 'Tooltip conjure frenzy warning ON'],
    'A warning when buying if it will put the bank under the amount needed for max "Conjure Baked Goods" rewards with Frenzy active',
    true,
  ),
  ToolWarnEdifice: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Tooltip edifice warning OFF', 'Tooltip edifice warning ON'],
    'A warning when buying if it will put the bank under the amount needed for "Spontaneous Edifice" to possibly give you your most expensive building',
    true,
  ),
  ToolWarnUser: new settingClasses.SettingInputNumber(
    0,
    'numscale',
    'Tooltip',
    'Tooltip warning at x times CPS: ',
    'Use this to show a customized warning if buying it will put the bank under the amount equal to value times cps; setting to 0 disables the function altogether',
    0,
    Infinity,
  ),
  ToolWarnBon: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Calculate tooltip warning with bonus CPS OFF', 'Calculate tooltip warning with bonus CPS ON'],
    'Calculate the warning with or without the bonus CPS you get from buying',
    true,
  ),
  ToolWarnPos: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'Tooltip',
    ['Tooltip warning position (left)', 'Tooltip warning position (bottom)'],
    'Placement of the warning boxes',
    false,
    () => {
      ToggleToolWarnPos();
    },
  ),
  TooltipGrim: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Grimoire tooltip information OFF', 'Grimoire tooltip information ON'],
    'Extra information in tooltip for grimoire',
    true,
  ),
  TooltipWrink: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Wrinkler tooltip OFF', 'Wrinkler tooltip ON'],
    'Shows the amount of cookies a wrinkler will give when popping it',
    true,
  ),
  TooltipLump: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Sugar lump tooltip OFF', 'Sugar lump tooltip ON'],
    'Shows the current Sugar Lump type in Sugar lump tooltip.',
    true,
  ),
  TooltipPlots: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Garden plots tooltip OFF', 'Garden plots tooltip ON'],
    'Shows a tooltip for plants that have a cookie reward.',
    true,
  ),
  TooltipStocks: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Stock market tooltips OFF', 'Stock market tooltips ON'],
    'Shows additional info in the stock market tooltips.',
    true,
  ),
  TooltipPantheon: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Pantheon tooltip OFF', 'Pantheon tooltip ON'],
    'Shows additional info in the pantheon tooltip',
    true,
  ),
  TooltipAscendButton: new settingClasses.SettingStandard(
    1,
    'bool',
    'Tooltip',
    ['Show Extra Info Ascend Tooltip OFF', 'Show Extra Info Ascend Tooltip ON'],
    'Shows additional info in the ascend tooltip',
    true,
  ),

  // Statistics
  Stats: new settingClasses.SettingStandard(
    1,
    'bool',
    'Statistics',
    ['Statistics OFF', 'Statistics ON'],
    'Extra Cookie Monster statistics!',
    true,
  ),
  AscendAdvisor: new settingClasses.SettingStandard(
    1,
    'bool',
    'Statistics',
    ['Ascension advisor OFF', 'Ascension advisor ON'],
    'Show the ascension advisor (optimal time to ascend, forecast and checklist) at the top of the statistics page',
    true,
  ),
  MissingUpgrades: new settingClasses.SettingStandard(
    1,
    'bool',
    'Statistics',
    ['Missing upgrades OFF', 'Missing upgrades ON'],
    'Shows missing upgrades in statistics menu',
    true,
  ),
  MissingAchievements: new settingClasses.SettingStandard(
    0,
    'bool',
    'Statistics',
    ['Missing Achievements OFF', 'Missing Normal Achievements ON'],
    'Shows missing normal achievements in statistics menu.',
    true,
  ),
  UpStats: new settingClasses.SettingStandard(
    1,
    'bool',
    'Statistics',
    ['Statistics update rate (default)', 'Statistics update rate (1s)'],
    'Default rate is once every 5 seconds',
    false,
  ),
  HeavenlyChipsTarget: new settingClasses.SettingInputNumber(
    1,
    'numscale',
    'Statistics',
    'Heavenly chips target: ',
    'Use this to set a heavenly chips target that will be counted towards in the "prestige" statsistics sections',
    1,
    Infinity,
  ),
  ShowMissedGC: new settingClasses.SettingStandard(
    1,
    'bool',
    'Statistics',
    ['Missed GC OFF', 'Missed GC ON'],
    'Show a stat in the statistics screen that counts how many golden cookies you have missed',
    true,
  ),

  // Notification
  Title: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationGeneral',
    ['Title OFF', 'Title ON', 'Title pinned tab highlight'],
    'Update title with colden cookie/season popup timers; pinned tab highlight only changes the title when a golden cookie/season popup spawns; "!" means that golden cookie/reindeer can spawn',
    true,
  ),
  GeneralSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationGeneral',
    ['Consider game volume setting OFF', 'Consider game volume setting ON'],
    'Turning this toggle to "off" makes Cookie Monster no longer consider the volume setting of the base game, allowing mod notifications to play with base game volume turned down',
    true,
  ),
  GCNotification: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'NotificationGC',
    ['Notification OFF', 'Notification ON'],
    'Create a notification when golden cookie spawns',
    true,
    () => {
      Config_CheckNotificationPermissions(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GCNotification,
      );
    },
  ),
  GCFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationGC',
    ['Flash OFF', 'Flash ON'],
    'Flash screen on golden cookie',
    true,
  ),
  ColourGCFlash: new settingClasses.SettingColours(
    '#ffffff',
    'colour',
    'NotificationGC',
    'The colour of the GC flash, standard colour is white',
  ),
  GCSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationGC',
    ['Sound OFF', 'Sound ON'],
    'Play a sound on golden cookie',
    true,
  ),
  GCVolume: new settingClasses.SettingVolume(100, 'vol', 'NotificationGC', [], 'Volume'),
  GCSoundURL: new settingClasses.SettingStandard(
    'https://freesound.org/data/previews/66/66717_931655-lq.mp3',
    'url',
    'NotificationGC',
    'Sound URL:',
    'URL of the sound to be played when a golden cookie spawns',
  ),
  FortuneNotification: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'NotificationFC',
    ['Notification OFF', 'Notification ON'],
    'Create a notification when fortune cookie is on the ticker',
    true,
    () => {
      Config_CheckNotificationPermissions(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.FortuneNotification,
      );
    },
  ),
  FortuneFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationFC',
    ['Flash OFF', 'Flash ON'],
    'Flash screen on fortune cookie spawn',
    true,
  ),
  ColourFortuneFlash: new settingClasses.SettingColours(
    '#ffffff',
    'colour',
    'NotificationFC',
    'The colour of the fortune flash, standard colour is white',
  ),
  FortuneSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationFC',
    ['Sound OFF', 'Sound ON'],
    'Play a sound on fortune cookie spawn',
    true,
  ),
  FortuneVolume: new settingClasses.SettingVolume(100, 'vol', 'NotificationFC', [], 'Volume'),
  FortuneSoundURL: new settingClasses.SettingStandard(
    'https://freesound.org/data/previews/174/174027_3242494-lq.mp3',
    'url',
    'NotificationFC',
    'Sound URL:',
    'URL of the sound to be played when the ticker has a fortune cookie',
  ),
  SeaNotification: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'NotificationSea',
    ['Notification OFF', 'Notification ON'],
    'Create a notification on season popup',
    true,
    () => {
      Config_CheckNotificationPermissions(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SeaNotification,
      );
    },
  ),
  SeaFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationSea',
    ['Flash OFF', 'Flash ON'],
    'Flash screen on season popup',
    true,
  ),
  ColourSeaFlash: new settingClasses.SettingColours(
    '#ffffff',
    'colour',
    'NotificationSea',
    'The colour of the season popup flash, standard colour is white',
  ),
  SeaSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationSea',
    ['Sound OFF', 'Sound ON'],
    'Play a sound on season popup',
    true,
  ),
  SeaVolume: new settingClasses.SettingVolume(100, 'vol', 'NotificationSea', [], 'Volume'),
  SeaSoundURL: new settingClasses.SettingStandard(
    'https://www.freesound.org/data/previews/121/121099_2193266-lq.mp3',
    'url',
    'NotificationSea',
    'Sound URL:',
    'URL of the sound to be played when on season popup spawns',
  ),
  GardFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationGard',
    ['Garden Tick Flash OFF', 'Flash ON'],
    'Flash screen on garden tick',
    true,
  ),
  ColourGardFlash: new settingClasses.SettingColours(
    '#ffffff',
    'colour',
    'NotificationGard',
    'The colour of the garden flash, standard colour is white',
  ),
  GardSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationGard',
    ['Sound OFF', 'Sound ON'],
    'Play a sound on garden tick',
    true,
  ),
  GardVolume: new settingClasses.SettingVolume(100, 'vol', 'NotificationGard', [], 'Volume'),
  GardSoundURL: new settingClasses.SettingStandard(
    'https://freesound.org/data/previews/103/103046_861714-lq.mp3',
    'url',
    'NotificationGard',
    'Garden Tick Sound URL:',
    'URL of the sound to be played when the garden ticks',
  ),
  MagicNotification: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'NotificationMagi',
    ['Notification OFF', 'Notification ON'],
    'Create a notification when magic reaches maximum',
    true,
    () => {
      Config_CheckNotificationPermissions(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.MagicNotification,
      );
    },
  ),
  MagicFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationMagi',
    ['Flash OFF', 'Flash ON'],
    'Flash screen when magic reaches maximum',
    true,
  ),
  ColourMagicFlash: new settingClasses.SettingColours(
    '#ffffff',
    'colour',
    'NotificationMagi',
    'The colour of the magic flash, standard colour is white',
  ),
  MagicSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationMagi',
    ['Sound OFF', 'Sound ON'],
    'Play a sound when magic reaches maximum',
    true,
  ),
  MagicVolume: new settingClasses.SettingVolume(100, 'vol', 'NotificationMagi', [], 'Volume'),
  MagicSoundURL: new settingClasses.SettingStandard(
    'https://freesound.org/data/previews/221/221683_1015240-lq.mp3',
    'url',
    'NotificationMagi',
    'Sound URL:',
    'URL of the sound to be played when magic reaches maxium',
  ),
  WrinklerNotification: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'NotificationWrink',
    ['Notification OFF', 'Notification ON'],
    'Create a notification when a wrinkler appears',
    true,
    () => {
      Config_CheckNotificationPermissions(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerNotification,
      );
    },
  ),
  WrinklerFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationWrink',
    ['Flash OFF', 'Flash ON'],
    'Flash screen when a wrinkler appears',
    true,
  ),
  ColourWrinklerFlash: new settingClasses.SettingColours(
    '#ffffff',
    'colour',
    'NotificationWrink',
    'The colour of the wrinkler flash, standard colour is white',
  ),
  WrinklerSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationWrink',
    ['Sound OFF', 'Sound ON'],
    'Play a sound when a wrinkler appears',
    true,
  ),
  WrinklerVolume: new settingClasses.SettingVolume(100, 'vol', 'NotificationWrink', [], 'Volume'),
  WrinklerSoundURL: new settingClasses.SettingStandard(
    'https://freesound.org/data/previews/124/124186_8043-lq.mp3',
    'url',
    'NotificationWrink',
    'Sound URL:',
    'URL of the sound to be played when a wrinkler appears',
  ),
  WrinklerMaxNotification: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'NotificationWrinkMax',
    ['Notification OFF', 'Notification ON'],
    'Create a notification when the maximum amount of wrinklers has appeared',
    true,
    () => {
      Config_CheckNotificationPermissions(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerMaxNotification,
      );
    },
  ),
  WrinklerMaxFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationWrinkMax',
    ['Flash OFF', 'Flash ON'],
    'Flash screen when the maximum amount of Wrinklers has appeared',
    true,
  ),
  ColourWrinklerMaxFlash: new settingClasses.SettingColours(
    '#ffffff',
    'colour',
    'NotificationWrinkMax',
    'The colour of the maximum wrinkler flash, standard colour is white',
  ),
  WrinklerMaxSound: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationWrinkMax',
    ['Sound OFF', 'Sound ON'],
    'Play a sound when the maximum amount of wrinklers has appeared',
    true,
  ),
  WrinklerMaxVolume: new settingClasses.SettingVolume(
    100,
    'vol',
    'NotificationWrinkMax',
    [],
    'Volume',
  ),
  WrinklerMaxSoundURL: new settingClasses.SettingStandard(
    'https://freesound.org/data/previews/152/152743_15663-lq.mp3',
    'url',
    'NotificationWrinkMax',
    'Sound URL:',
    'URL of the sound to be played when the maximum amount of wrinklers has appeared',
  ),
  AscendNote: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationAscend',
    ['In-game note OFF', 'In-game note ON'],
    'Show a note in the game when the optimal time to ascend is reached',
    true,
  ),
  AscendNotification: new settingClasses.SettingStandardWithFunc(
    0,
    'bool',
    'NotificationAscend',
    ['Notification OFF', 'Notification ON'],
    'Create a notification when the optimal time to ascend is reached',
    true,
    () => {
      Config_CheckNotificationPermissions(
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AscendNotification,
      );
    },
  ),
  AscendFlash: new settingClasses.SettingStandard(
    1,
    'bool',
    'NotificationAscend',
    ['Flash OFF', 'Flash ON'],
    'Flash screen when the optimal time to ascend is reached',
    true,
  ),
  ColourAscendFlash: new settingClasses.SettingColours(
    '#ffd700',
    'colour',
    'NotificationAscend',
    'The colour of the ascension flash, standard colour is gold',
  ),
  AscendSound: new settingClasses.SettingStandard(
    0,
    'bool',
    'NotificationAscend',
    ['Sound OFF', 'Sound ON'],
    'Play a sound when the optimal time to ascend is reached',
    true,
  ),
  AscendVolume: new settingClasses.SettingVolume(100, 'vol', 'NotificationAscend', [], 'Volume'),
  AscendSoundURL: new settingClasses.SettingStandard(
    'https://freesound.org/data/previews/221/221683_1015240-lq.mp3',
    'url',
    'NotificationAscend',
    'Sound URL:',
    'URL of the sound to be played when the optimal time to ascend is reached',
  ),

  // Autoplay
  AutoClick: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto-click OFF', 'Auto-click ON'],
    'Clicks the big cookie automatically (without the click sound)',
    true,
  ),
  AutoClickRate: new settingClasses.SettingInputNumber(
    20,
    'numscale',
    'Autoplay',
    'Clicks per second: ',
    'How fast auto-click clicks; the game ignores more than 50 clicks per second',
    1,
    50,
  ),
  AutoBuy: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto-buy OFF', 'Auto-buy ON'],
    'Buys the building or upgrade with the best payback period as soon as it is affordable. Skips upgrades that ask for confirmation (such as One mind, which starts the Grandmapocalypse), switches, sugar lump costs and the Chocolate egg. Pauses while the store is in sell mode',
    true,
  ),
  AutoBuyLuckyBank: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Keep "Lucky!" bank OFF', 'Keep "Lucky!" bank ON'],
    'Keeps enough cookies banked for a maximum "Lucky!" reward whenever banked cookies pay back faster through golden cookies than the next purchase would',
    true,
  ),
  AutoGolden: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto golden cookies OFF', 'Auto golden cookies ON'],
    'Clicks golden cookies and reindeer as soon as they appear (golden cookie flashes and sounds are skipped)',
    true,
  ),
  AutoGoldenWrath: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Click wrath cookies OFF', 'Click wrath cookies ON'],
    'Also click wrath cookies, which only appear during the Grandmapocalypse',
    true,
  ),
  AutoAscend: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto-ascend OFF', 'Auto-ascend ON'],
    'Ascends once the Ascension Advisor has said it is optimal for 10 seconds: pops normal wrinklers and buys the Chocolate egg first, spends heavenly chips (Legacy and production upgrades first, several at once), fills the permanent upgrade slots and reincarnates',
    true,
  ),
  AutoElder: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Grandmapocalypse OFF', 'Grandmapocalypse ON'],
    'Researches up to the Elder Pact (wrath cookies beat golden ones when every cookie is clicked, and wrinklers multiply income about six times), earns the elder achievements, and pops a wrinkler when cashing it in beats keeping it',
    true,
  ),
  AutoDragon: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto dragon OFF', 'Auto dragon ON'],
    'Hatches and trains the dragon every run when buying back the sacrificed buildings costs little (up to an hour of income on the way to Radiant Appetite or Dragon Guts) and picks the auras worth most',
    true,
  ),
  AutoSeasons: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto seasons OFF', 'Auto seasons ON'],
    'Every run: Christmas until Santa is maxed, a short Valentine\'s day for the heart biscuits, Easter until 7 eggs while "Egging on" is missing, then Christmas for its reindeer (needs the Season switcher to switch; otherwise uses the natural season)',
    true,
  ),
  AutoLumps: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto sugar lumps OFF', 'Auto sugar lumps ON'],
    'Harvests ripe sugar lumps and spends them: minigames first, then the building level with the most CpS per lump',
    true,
  ),
  AutoPantheon: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto Pantheon OFF', 'Auto Pantheon ON'],
    'Slots the gods that give the most long-run income, spending worship swaps only when it pays',
    true,
  ),
  AutoGarden: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto Garden OFF', 'Auto Garden ON'],
    'Plants the seed worth most over its mature life when that beats its price, picks plants while mature just before they die (counts toward harvest achievements and unlocks new mutations), and keeps one tile free for mutations',
    true,
  ),
  AutoGodzamok: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto Godzamok OFF', 'Auto Godzamok ON'],
    'With Godzamok slotted, sells and buys back every building type whose round trip pays, every frame, so his click buff keeps growing (and lets the Pantheon slot him for it)',
    true,
  ),
  AutoChallenge: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto Born again challenge OFF', 'Auto Born again challenge ON'],
    'Plays one Born again run for Neverclick and Hardcore (about 4 hours, no clicks past 15, no upgrades) once the two achievements are worth more than the time it takes, then returns to normal runs',
    true,
  ),
  AutoMarket: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto Stock Market OFF', 'Auto Stock Market ON'],
    'Buys goods at 60% of their resting value or less and sells them at or above it, holding at most 10% of the bank in goods',
    true,
  ),
  AutoGrimoire: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Auto Grimoire OFF', 'Auto Grimoire ON'],
    'Casts Force the Hand of Fate whenever magic is full (magic refills fastest near the top of the bar)',
    true,
  ),
  AutoAchievements: new settingClasses.SettingStandard(
    1,
    'bool',
    'Autoplay',
    ['Easy achievements OFF', 'Easy achievements ON'],
    'Takes the achievements that only need an action (each adds milk, about +2% CpS with many kittens): the news ticker, the tiny cookie, the madeleine, selling a grandma, a last-second golden cookie, poking a wrinkler',
    true,
  ),

  // Miscellaneous
  BulkBuyBlock: new settingClasses.SettingStandard(
    1,
    'bool',
    'Miscellaneous',
    ['Block bulk buying OFF', 'Block bulk buying ON'],
    "Block clicking bulk buying when you can't buy all. This prevents buying 7 of a building when you are in buy-10 or buy-100 mode.",
    true,
  ),
  FavouriteSettings: new settingClasses.SettingStandardWithFunc(
    1,
    'bool',
    'Miscellaneous',
    [
      'Favourite settings section OFF',
      'Favourite settings section ON',
      'Favourite settings section ON (Locked)',
    ],
    "Show stars before each setting which allows selecting it for a 'favourites' section at the top of the Cookie Monster settings. Setting this to Locked removes the stars but shows the 'favourites' section",
    true,
    () => {
      Game.UpdateMenu();
    },
  ),
};

/* harmony default export */ const Data_settings = (settings_settings);

;// ./src/Disp/HelperFunctions/UpdateColours.js



/**
 * This function changes/refreshes colours if the user has set new standard colours
 * The function is therefore called by a change in CM.Options.Colours
 */
function UpdateColours() {
  let str = '';
  for (let i = 0; i < ColoursOrdering.length; i++) {
    str += `.${ColourTextPre}${ColoursOrdering[i]} { color: ${
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings[
        `Colour${ColoursOrdering[i]}`
      ]
    }; }\n`;
  }
  for (let i = 0; i < ColoursOrdering.length; i++) {
    str += `.${ColourBackPre}${ColoursOrdering[i]} { background-color: ${
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings[
        `Colour${ColoursOrdering[i]}`
      ]
    }; }\n`;
  }
  for (let i = 0; i < ColoursOrdering.length; i++) {
    str += `.${ColourBorderPre}${ColoursOrdering[i]} { border: 1px solid ${
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings[
        `Colour${ColoursOrdering[i]}`
      ]
    }; }\n`;
  }
  l('CMCSS').textContent = str;
  UpdateBuildings(); // Class has been already set
}

;// ./src/Disp/MenuSections/createMenuOptions.js






/**
 * Creates the <div> to be added to the Options section
 * @returns {object} menuDiv	Object of the <div> of Cookie Monster in options tab
 */
function createMenuOptions() {
  const menuDiv = menuFunctions.createModMenuSection('cookieMonsterMod', 'Cookie Monster', 'optionsMenu');

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.optionsMenu) {
    Object.keys(ConfigGroups).forEach((group) => {
      if (group === 'Favourite') {
        if (
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.favouriteSettings.length !==
            0 &&
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.FavouriteSettings > 0
        ) {
          menuDiv.appendChild(
            menuFunctions.listings.createOptionsSubHeader('cookieMonsterMod', group, ConfigGroups[group]),
          );
          if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers[group])
            for (
              let index = 0;
              index <
              Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.favouriteSettings.length;
              index++
            ) {
              menuDiv.appendChild(
                menuFunctions.listings.createOptionsListing(
                  'cookieMonsterMod',
                  Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.favouriteSettings[
                    index
                  ],
                  Data_settings,
                  UpdateColours,
                  RefreshScale,
                ),
              );
            }
        }
      } else {
        menuDiv.appendChild(
          menuFunctions.listings.createOptionsSubHeader('cookieMonsterMod', group, ConfigGroups[group]),
        );
        if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers[group]) {
          // 0 is show, 1 is collapsed
          // Make sub-sections of Notification section
          if (group === 'Notification') {
            Object.keys(ConfigGroupsNotification).forEach((subGroup) => {
              const subGroupObject = menuFunctions.listings.createOptionsSubHeader(
                'cookieMonsterMod',
                subGroup,
                ConfigGroupsNotification[subGroup],
              );
              subGroupObject.style.fontSize = '15px';
              subGroupObject.style.opacity = '0.5';
              menuDiv.appendChild(subGroupObject);
              if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers[subGroup]) {
                Object.keys(Data_settings).forEach((option) => {
                  if (Data_settings[option].group === subGroup)
                    menuDiv.appendChild(
                      menuFunctions.listings.createOptionsListing(
                        'cookieMonsterMod',
                        option,
                        Data_settings,
                        UpdateColours,
                        RefreshScale,
                      ),
                    );
                });
              }
            });
          } else {
            Object.keys(Data_settings).forEach((option) => {
              if (Data_settings[option].group === group)
                menuDiv.appendChild(
                  menuFunctions.listings.createOptionsListing(
                    'cookieMonsterMod',
                    option,
                    Data_settings,
                    UpdateColours,
                    RefreshScale,
                  ),
                );
            });
          }
        }
      }
    });
  }
  return menuDiv;
}

;// ./src/Sim/SimulationEvents/ResetAscension.js







/**
 * This function calculates the cookies per click difference betwene current and after a ascension
 * It is called by CM.Disp.CreateStatsPrestigeSection()
 * @param	{number}	newHeavenlyChips	The total heavenly chips after ascension
 * @returns	{number}	ResetCPS			The CPS difference after reset
 */
function ResetBonus(newHeavenlyChips) {
  // Calculate CPS with all Heavenly upgrades
  let curCPS = Game.cookiesPs;

  CopyData();

  if (SimUpgrades['Heavenly key'].bought === 0) {
    SimUpgrades['Heavenly chip secret'].bought = 1;
    SimUpgrades['Heavenly cookie stand'].bought = 1;
    SimUpgrades['Heavenly bakery'].bought = 1;
    SimUpgrades['Heavenly confectionery'].bought = 1;
    SimUpgrades['Heavenly key'].bought = 1;

    CalculateGains();

    curCPS = SimCookiesPs;

    CopyData();
  }

  if (CacheRealCookiesEarned >= 1000000) SimWin('Sacrifice');
  if (CacheRealCookiesEarned >= 1000000000) SimWin('Oblivion');
  if (CacheRealCookiesEarned >= 1000000000000) SimWin('From scratch');
  if (CacheRealCookiesEarned >= 1000000000000000) SimWin('Nihilism');
  if (CacheRealCookiesEarned >= 1000000000000000000) SimWin('Dematerialize');
  if (CacheRealCookiesEarned >= 1000000000000000000000) SimWin('Nil zero zilch');
  if (CacheRealCookiesEarned >= 1000000000000000000000000) SimWin('Transcendence');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000) SimWin('Obliterate');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000) SimWin('Negative void');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000) SimWin('To crumbs, you say?');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000000) SimWin('You get nothing');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000000000)
    SimWin('Humble rebeginnings');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000000000000)
    SimWin('The end of the world');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000000000000000)
    SimWin("Oh, you're back");
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000000000000000000)
    SimWin('Lazarus');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000000000000000000000)
    SimWin('Smurf account');
  if (CacheRealCookiesEarned >= 1000000000000000000000000000000000000000000000000000000)
    SimWin("If at first you don't succeed");

  SimUpgrades['Heavenly chip secret'].bought = 1;
  SimUpgrades['Heavenly cookie stand'].bought = 1;
  SimUpgrades['Heavenly bakery'].bought = 1;
  SimUpgrades['Heavenly confectionery'].bought = 1;
  SimUpgrades['Heavenly key'].bought = 1;

  SimPrestige = newHeavenlyChips;

  const lastAchievementsOwned = SimAchievementsOwned;

  CalculateGains();

  CheckOtherAchiev();

  if (lastAchievementsOwned !== SimAchievementsOwned) {
    CalculateGains();
  }

  const ResetCPS = SimCookiesPs - curCPS;

  // Reset Pretige level after calculation as it is used in CM.Sim.CalculateGains() so can't be local
  SimPrestige = Game.prestige;

  return ResetCPS;
}

;// ./src/Disp/HelperFunctions/CalculateLuckyLevels.js
const SPECIAL_DIGIT = 7;

/**
 * Count the number of 7s in any number
 * @param	{number}	number	The number to count sevens for
 * @returns	{number}	The number of 7s in the provided number
 */
function CountSevens(number) {
  return String(number).split(String(SPECIAL_DIGIT)).length - 1;
}

/**
 * Calculate the delta for the next number where the given digit is a 7
 * @param	{number}	number			The starting number to calculate the delta for
 * @param	{number}	digitPlace	1 for ones place, 10 for tens place, 100 for hundreds place, etc
 * @returns	{number}	The calculated delta
 */
function CalculateSevenDelta(number, digitPlace) {
  const target = SPECIAL_DIGIT * digitPlace;
  const modulus = digitPlace * 10;

  let delta = target - (number % modulus) + (number % digitPlace);
  if (delta < 0) delta += modulus;

  return delta;
}

/**
 * This function calculates each of the next "lucky" prestige levels
 * @param	{number}	currentLevel	The user's prestige level, including levels earned since the last ascension
 * @returns	{{number}, {number}, {number}}	luckyDigit, luckyNumber, luckyPayout	The next eligible level for each upgrade
 */
function CalculateLuckyLevels(currentLevel) {
  const result = {};
  let sevenCount = CountSevens(currentLevel);
  const numberOfDigits = Math.max(Math.floor(Math.log10(Math.abs(currentLevel))), 0) + 1;

  if (sevenCount >= 1) {
    result.luckyDigit = currentLevel;
    if (sevenCount >= 2) {
      result.luckyNumber = currentLevel;
      if (sevenCount >= 4) {
        result.luckyPayout = currentLevel;
        return result;
      }
    }
  }

  // Consider only top 15 digits if it is big number
  let localLevel;
  if (numberOfDigits >= 16) {
    localLevel = Math.ceil(currentLevel / 10 ** (numberOfDigits - 15));
  } else {
    localLevel = currentLevel;
  }
  sevenCount = CountSevens(localLevel);

  if (result.luckyDigit === undefined) {
    if (sevenCount < 1) {
      const delta = CalculateSevenDelta(localLevel, 1);

      localLevel += delta;
      sevenCount = CountSevens(localLevel);
    }

    result.luckyDigit = localLevel;
    if (numberOfDigits >= 16) {
      result.luckyDigit *= 10 ** Number(numberOfDigits - 15);
    }
  }

  if (result.luckyNumber === undefined) {
    while (sevenCount < 2) {
      let delta = CalculateSevenDelta(localLevel, 1);
      if (delta === 0) delta = CalculateSevenDelta(localLevel, 10);

      localLevel += delta;
      sevenCount = CountSevens(localLevel);
    }

    result.luckyNumber = localLevel;
    if (numberOfDigits >= 16) {
      result.luckyNumber *= 10 ** Number(numberOfDigits - 15);
    }
  }

  let digitPlace = 1;
  while (sevenCount < 4) {
    const delta = CalculateSevenDelta(localLevel, digitPlace);
    if (delta === 0) {
      digitPlace *= 10;
    } else {
      localLevel += delta;
      sevenCount = CountSevens(localLevel);
    }
  }

  result.luckyPayout = localLevel;
  if (numberOfDigits >= 16) {
    result.luckyPayout *= 10 ** Number(numberOfDigits - 15);
  }

  return result;
}

;// ./src/Config/ToggleSetting.js


/** Functions related to toggling or changing an individual setting */

/** Used to name certain DOM or outside facing elements and refer to them */
const ConfigPrefix = 'CMConfig';

/**
 * This function toggles header options by incrementing them with 1 and handling changes
 * It is called by the onclick event of the +/- next to headers
 * @param 	{string}	config	The name of the header
 */
function ToggleHeader(config) {
  Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers[config] += 1;
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers[config] > 1)
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers[config] = 0;
  saveAndLoadingFunctions.saveFramework();
}

;// ./src/Disp/MenuSections/Statistics/CreateDOMElements.js
/** Section: Functions related to the creation of basic DOM elements page */





/**
 * This function creates a header-object for the stats page
 * It is called by CM.Disp.AddMenuStats()
 * @param 	{string}		config	The name of the Config-group
 * @param 	{string}		text	The to-be displayed name of the header
 * @returns	{object}		div		The header object
 */
function StatsHeader(text, config) {
  const div = document.createElement('div');
  div.className = 'title';
  div.style.padding = '0px 16px';
  div.style.opacity = '0.7';
  div.style.fontSize = '17px';
  div.style.fontFamily = '"Kavoon", Georgia, serif';
  div.appendChild(document.createTextNode(`${text} `));
  const span = document.createElement('span');
  span.style.cursor = 'pointer';
  span.style.display = 'inline-block';
  span.style.height = '14px';
  span.style.width = '14px';
  span.style.borderRadius = '7px';
  span.style.textAlign = 'center';
  span.style.backgroundColor = '#C0C0C0';
  span.style.color = 'black';
  span.style.fontSize = '13px';
  span.style.verticalAlign = 'middle';
  span.textContent = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers[config]
    ? '-'
    : '+';
  span.onclick = function () {
    ToggleHeader(config);
    Game.UpdateMenu();
  };
  div.appendChild(span);
  return div;
}

/**
 * This function creates an stats-listing-object for the stats page
 * It is called by CM.Disp.AddMenuStats()
 * @param 	{string}		type		The type fo the listing
 * @param 	{string}		name		The name of the option
 * @param 	{object}		text		The text-object of the option
 * @param 	{string}		placeholder	The id of the to-be displayed tooltip if applicable
 * @returns	{object}		div			The option object
 */
function StatsListing(type, name, text, placeholder) {
  const div = document.createElement('div');
  div.className = 'listing';

  const listingName = document.createElement('b');
  listingName.textContent = name;
  div.appendChild(listingName);
  if (type === 'withTooltip') {
    div.className = 'listing';
    div.appendChild(document.createTextNode(' '));

    const tooltip = document.createElement('span');
    tooltip.onmouseout = function () {
      Game.tooltip.hide();
    };
    tooltip.onmouseover = function () {
      Game.tooltip.draw(this, escape(SimpleTooltipElements[placeholder].innerHTML));
    };
    tooltip.style.cursor = 'default';
    tooltip.style.display = 'inline-block';
    tooltip.style.height = '10px';
    tooltip.style.width = '10px';
    tooltip.style.borderRadius = '5px';
    tooltip.style.textAlign = 'center';
    tooltip.style.backgroundColor = '#C0C0C0';
    tooltip.style.color = 'black';
    tooltip.style.fontSize = '9px';
    tooltip.style.verticalAlign = 'bottom';
    tooltip.textContent = '?';
    div.appendChild(tooltip);
  }
  div.appendChild(document.createTextNode(': '));
  div.appendChild(text);
  return div;
}

/**
 * This function creates an stats-listing-object for the stats page for missing items displays
 * It is called by CM.Disp.AddMenuStats()
 * @param 	{string}		type		The type fo the listing
 * @param 	{string}		name		The name of the option
 * @param 	{object}		text		The text-object of the option
 * @param 	{bool}		  current Whether the season of the item is the current season
 * @returns	{object}		div			The option object
 */
function StatsMissDispListing(type, name, text, current) {
  const div = document.createElement('div');
  div.className = 'listing';

  const listingName = document.createElement('b');
  listingName.textContent = name;
  if (current === true)
    listingName.style.color =
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ColourGreen;
  div.appendChild(listingName);
  div.appendChild(document.createTextNode(': '));
  div.appendChild(text);
  return div;
}

/**
 * This function creates a tooltip containing all missing holiday items contained in the list theMissDisp
 * @param 	{list}			theMissDisp		A list of the missing holiday items
 * @returns	{object}		frag			The tooltip object
 */
function StatsMissDisp(theMissDisp) {
  const frag = document.createDocumentFragment();
  frag.appendChild(document.createTextNode(`${theMissDisp.length} `));
  const span = document.createElement('span');
  span.onmouseout = function () {
    Game.tooltip.hide();
  };
  const placeholder = document.createElement('div');
  const missing = document.createElement('div');
  missing.style.minWidth = '140px';
  missing.style.marginBottom = '4px';
  const title = document.createElement('div');
  title.className = 'name';
  title.style.marginBottom = '4px';
  title.style.textAlign = 'center';
  title.textContent = 'Missing';
  missing.appendChild(title);
  Object.keys(theMissDisp).forEach((i) => {
    const div = document.createElement('div');
    div.style.textAlign = 'center';
    div.appendChild(document.createTextNode(theMissDisp[i]));
    missing.appendChild(div);
  });
  placeholder.appendChild(missing);
  span.onmouseover = function () {
    Game.tooltip.draw(this, escape(placeholder.innerHTML));
  };
  span.style.cursor = 'default';
  span.style.display = 'inline-block';
  span.style.height = '10px';
  span.style.width = '10px';
  span.style.borderRadius = '5px';
  span.style.textAlign = 'center';
  span.style.backgroundColor = '#C0C0C0';
  span.style.color = 'black';
  span.style.fontSize = '9px';
  span.style.verticalAlign = 'bottom';
  span.textContent = '?';
  frag.appendChild(span);
  return frag;
}

;// ./src/Disp/MenuSections/Statistics/CreateStatsSections.js
/** Functions to create the individual sections of the Statistics page */













/**
 * This function creates the "Lucky" section of the stats page
 * @returns	{object}	section		The object contating the Lucky section
 */
function LuckySection() {
  // This sets which tooltip to display for certain stats
  const goldCookTooltip = Game.auraMult("Dragon's Fortune")
    ? 'GoldCookDragonsFortuneTooltipPlaceholder'
    : 'GoldCookTooltipPlaceholder';

  const section = document.createElement('div');
  section.className = 'CMStatsLuckySection';

  const luckyColour = Game.cookies + GetWrinkConfigBank() < CacheLucky ? ColourRed : ColourGreen;
  const luckyTime =
    Game.cookies + GetWrinkConfigBank() < CacheLucky
      ? FormatTime((CacheLucky - (Game.cookies + GetWrinkConfigBank())) / GetCPS())
      : '';
  const luckyReqFrag = document.createDocumentFragment();
  const luckyReqSpan = document.createElement('span');
  luckyReqSpan.style.fontWeight = 'bold';
  luckyReqSpan.className = ColourTextPre + luckyColour;
  luckyReqSpan.textContent = Beautify_Beautify(CacheLucky);
  luckyReqFrag.appendChild(luckyReqSpan);
  if (luckyTime !== '') {
    const luckyReqSmall = document.createElement('small');
    luckyReqSmall.textContent = ` (${luckyTime})`;
    luckyReqFrag.appendChild(luckyReqSmall);
  }
  section.appendChild(
    StatsListing('withTooltip', '"Lucky!" cookies required', luckyReqFrag, goldCookTooltip),
  );

  const luckyColourFrenzy =
    Game.cookies + GetWrinkConfigBank() < CacheLuckyFrenzy ? ColourRed : ColourGreen;
  const luckyTimeFrenzy =
    Game.cookies + GetWrinkConfigBank() < CacheLuckyFrenzy
      ? FormatTime((CacheLuckyFrenzy - (Game.cookies + GetWrinkConfigBank())) / GetCPS())
      : '';
  const luckyReqFrenFrag = document.createDocumentFragment();
  const luckyReqFrenSpan = document.createElement('span');
  luckyReqFrenSpan.style.fontWeight = 'bold';
  luckyReqFrenSpan.className = ColourTextPre + luckyColourFrenzy;
  luckyReqFrenSpan.textContent = Beautify_Beautify(CacheLuckyFrenzy);
  luckyReqFrenFrag.appendChild(luckyReqFrenSpan);
  if (luckyTimeFrenzy !== '') {
    const luckyReqFrenSmall = document.createElement('small');
    luckyReqFrenSmall.textContent = ` (${luckyTimeFrenzy})`;
    luckyReqFrenFrag.appendChild(luckyReqFrenSmall);
  }
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Lucky!" cookies required (frenzy)',
      luckyReqFrenFrag,
      goldCookTooltip,
    ),
  );

  const luckySplit = CacheLuckyReward !== CacheLuckyWrathReward;

  const luckyRewardMaxSpan = document.createElement('span');
  luckyRewardMaxSpan.style.fontWeight = 'bold';

  luckyRewardMaxSpan.textContent =
    Beautify_Beautify(CacheLuckyReward) + (luckySplit ? ` / ${Beautify_Beautify(CacheLuckyWrathReward)}` : '');
  section.appendChild(
    StatsListing(
      'withTooltip',
      `"Lucky!" reward (max)${luckySplit ? ' (golden / wrath)' : ''}`,
      luckyRewardMaxSpan,
      goldCookTooltip,
    ),
  );

  const luckyRewardFrenzyMaxSpan = document.createElement('span');
  luckyRewardFrenzyMaxSpan.style.fontWeight = 'bold';

  luckyRewardFrenzyMaxSpan.textContent =
    Beautify_Beautify(CacheLuckyRewardFrenzy) +
    (luckySplit ? ` / ${Beautify_Beautify(CacheLuckyWrathRewardFrenzy)}` : '');
  section.appendChild(
    StatsListing(
      'withTooltip',
      `"Lucky!" reward (max) (frenzy)${luckySplit ? ' (golden / wrath)' : ''}`,
      luckyRewardFrenzyMaxSpan,
      goldCookTooltip,
    ),
  );

  const luckyCurBase =
    Math.min(
      (Game.cookies + GetWrinkConfigBank()) * 0.15,
      CacheNoGoldSwitchCookiesPS * CacheDragonsFortuneMultAdjustment * 60 * 15,
    ) + 13;
  const luckyCurSpan = document.createElement('span');
  luckyCurSpan.style.fontWeight = 'bold';

  luckyCurSpan.textContent =
    Beautify_Beautify(CacheGoldenCookiesMult * luckyCurBase) +
    (luckySplit ? ` / ${Beautify_Beautify(CacheWrathCookiesMult * luckyCurBase)}` : '');
  section.appendChild(
    StatsListing(
      'withTooltip',
      `"Lucky!" reward (cur)${luckySplit ? ' (golden / wrath)' : ''}`,
      luckyCurSpan,
      goldCookTooltip,
    ),
  );
  return section;
}

/**
 * This function creates the "Chain" section of the stats page
 * @returns	{object}	section		The object contating the Chain section
 */
function ChainSection() {
  // This sets which tooltip to display for certain stats
  const goldCookTooltip = Game.auraMult("Dragon's Fortune")
    ? 'GoldCookDragonsFortuneTooltipPlaceholder'
    : 'GoldCookTooltipPlaceholder';

  const section = document.createElement('div');
  section.className = 'CMStatsChainSection';

  const chainColour =
    Game.cookies + GetWrinkConfigBank() < CacheChainRequired ? ColourRed : ColourGreen;
  const chainTime =
    Game.cookies + GetWrinkConfigBank() < CacheChainRequired
      ? FormatTime((CacheChainRequired - (Game.cookies + GetWrinkConfigBank())) / GetCPS())
      : '';
  const chainReqFrag = document.createDocumentFragment();
  const chainReqSpan = document.createElement('span');
  chainReqSpan.style.fontWeight = 'bold';
  chainReqSpan.className = ColourTextPre + chainColour;
  chainReqSpan.textContent = Beautify_Beautify(CacheChainRequired);
  chainReqFrag.appendChild(chainReqSpan);
  if (chainTime !== '') {
    const chainReqSmall = document.createElement('small');
    chainReqSmall.textContent = ` (${chainTime})`;
    chainReqFrag.appendChild(chainReqSmall);
  }
  section.appendChild(
    StatsListing('withTooltip', '"Chain" cookies required', chainReqFrag, goldCookTooltip),
  );

  const chainWrathColour =
    Game.cookies + GetWrinkConfigBank() < CacheChainWrathRequired ? ColourRed : ColourGreen;
  const chainWrathTime =
    Game.cookies + GetWrinkConfigBank() < CacheChainWrathRequired
      ? FormatTime((CacheChainWrathRequired - (Game.cookies + GetWrinkConfigBank())) / GetCPS())
      : '';
  const chainWrathReqFrag = document.createDocumentFragment();
  const chainWrathReqSpan = document.createElement('span');
  chainWrathReqSpan.style.fontWeight = 'bold';
  chainWrathReqSpan.className = ColourTextPre + chainWrathColour;
  chainWrathReqSpan.textContent = Beautify_Beautify(CacheChainWrathRequired);
  chainWrathReqFrag.appendChild(chainWrathReqSpan);
  if (chainWrathTime !== '') {
    const chainWrathReqSmall = document.createElement('small');
    chainWrathReqSmall.textContent = ` (${chainWrathTime})`;
    chainWrathReqFrag.appendChild(chainWrathReqSmall);
  }
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Chain" cookies required (Wrath)',
      chainWrathReqFrag,
      goldCookTooltip,
    ),
  );

  const chainColourFrenzy =
    Game.cookies + GetWrinkConfigBank() < CacheChainFrenzyRequired ? ColourRed : ColourGreen;
  const chainTimeFrenzy =
    Game.cookies + GetWrinkConfigBank() < CacheChainFrenzyRequired
      ? FormatTime((CacheChainFrenzyRequired - (Game.cookies + GetWrinkConfigBank())) / GetCPS())
      : '';
  const chainReqFrenFrag = document.createDocumentFragment();
  const chainReqFrenSpan = document.createElement('span');
  chainReqFrenSpan.style.fontWeight = 'bold';
  chainReqFrenSpan.className = ColourTextPre + chainColourFrenzy;
  chainReqFrenSpan.textContent = Beautify_Beautify(CacheChainFrenzyRequired);
  chainReqFrenFrag.appendChild(chainReqFrenSpan);
  if (chainTimeFrenzy !== '') {
    const chainReqFrenSmall = document.createElement('small');
    chainReqFrenSmall.textContent = ` (${chainTimeFrenzy})`;
    chainReqFrenFrag.appendChild(chainReqFrenSmall);
  }
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Chain" cookies required (Frenzy)',
      chainReqFrenFrag,
      goldCookTooltip,
    ),
  );

  const chainWrathColourFrenzy =
    Game.cookies + GetWrinkConfigBank() < CacheChainFrenzyWrathRequired ? ColourRed : ColourGreen;
  const chainWrathTimeFrenzy =
    Game.cookies + GetWrinkConfigBank() < CacheChainFrenzyWrathRequired
      ? FormatTime(
          (CacheChainFrenzyWrathRequired - (Game.cookies + GetWrinkConfigBank())) / GetCPS(),
        )
      : '';
  const chainWrathReqFrenFrag = document.createDocumentFragment();
  const chainWrathReqFrenSpan = document.createElement('span');
  chainWrathReqFrenSpan.style.fontWeight = 'bold';
  chainWrathReqFrenSpan.className = ColourTextPre + chainWrathColourFrenzy;
  chainWrathReqFrenSpan.textContent = Beautify_Beautify(CacheChainFrenzyWrathRequired);
  chainWrathReqFrenFrag.appendChild(chainWrathReqFrenSpan);
  if (chainWrathTimeFrenzy !== '') {
    const chainWrathReqFrenSmall = document.createElement('small');
    chainWrathReqFrenSmall.textContent = ` (${chainWrathTimeFrenzy})`;
    chainWrathReqFrenFrag.appendChild(chainWrathReqFrenSmall);
  }
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Chain" cookies required (frenzy) (Wrath)',
      chainWrathReqFrenFrag,
      goldCookTooltip,
    ),
  );

  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Chain" reward (max) (golden / wrath)',
      document.createTextNode(
        `${Beautify_Beautify(CacheChainMaxReward[0])} / ${Beautify_Beautify(CacheChainWrathMaxReward[0])}`,
      ),
      goldCookTooltip,
    ),
  );

  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Chain" reward (max) (frenzy) (golden / wrath)',
      document.createTextNode(
        `${Beautify_Beautify(CacheChainFrenzyMaxReward[0])} / ${Beautify_Beautify(CacheChainFrenzyMaxReward[0])}`,
      ),
      goldCookTooltip,
    ),
  );

  const chainCurMax = Math.min(
    Game.cookiesPs * 60 * 60 * 6 * CacheDragonsFortuneMultAdjustment,
    Game.cookies * 0.5,
  );
  const chainCur = MaxChainCookieReward(7, chainCurMax, CacheGoldenCookiesMult)[0];
  const chainCurWrath = MaxChainCookieReward(6, chainCurMax, CacheWrathCookiesMult)[0];
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Chain" reward (cur) (golden / wrath)',
      document.createTextNode(`${Beautify_Beautify(chainCur)} / ${Beautify_Beautify(chainCurWrath)}`),
      goldCookTooltip,
    ),
  );

  section.appendChild(
    StatsListing(
      'withTooltip',
      'CPS needed for next level (g / w)',
      document.createTextNode(
        `${Beautify_Beautify(CacheChainRequiredNext)} / ${Beautify_Beautify(CacheChainWrathRequiredNext)}`,
      ),
      'ChainNextLevelPlaceholder',
    ),
  );
  section.appendChild(
    StatsListing(
      'withTooltip',
      'CPS needed for next level (frenzy) (g / w)',
      document.createTextNode(
        `${Beautify_Beautify(CacheChainFrenzyRequiredNext)} / ${Beautify_Beautify(
          CacheChainFrenzyWrathRequiredNext,
        )}`,
      ),
      'ChainNextLevelPlaceholder',
    ),
  );
  return section;
}

/**
 * This function creates the "Spells" section of the stats page
 * @returns	{object}	section		The object contating the Spells section
 */
function SpellsSection() {
  const section = document.createElement('div');
  section.className = 'CMStatsSpellsSection';

  const conjureColour =
    Game.cookies + GetWrinkConfigBank() < CacheConjure ? ColourRed : ColourGreen;
  const conjureTime =
    Game.cookies + GetWrinkConfigBank() < CacheConjure
      ? FormatTime((CacheConjure - (Game.cookies + GetWrinkConfigBank())) / GetCPS())
      : '';

  const conjureReqFrag = document.createDocumentFragment();
  const conjureReqSpan = document.createElement('span');
  conjureReqSpan.style.fontWeight = 'bold';
  conjureReqSpan.className = ColourTextPre + conjureColour;
  conjureReqSpan.textContent = Beautify_Beautify(CacheConjure);
  conjureReqFrag.appendChild(conjureReqSpan);
  if (conjureTime !== '') {
    const conjureReqSmall = document.createElement('small');
    conjureReqSmall.textContent = ` (${conjureTime})`;
    conjureReqFrag.appendChild(conjureReqSmall);
  }
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Conjure Baked Goods" cookies required',
      conjureReqFrag,
      'GoldCookTooltipPlaceholder',
    ),
  );
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Conjure Baked Goods" reward (max)',
      document.createTextNode(Beautify_Beautify(CacheConjureReward)),
      'GoldCookTooltipPlaceholder',
    ),
  );

  const conjureFrenzyColour =
    Game.cookies + GetWrinkConfigBank() < CacheConjure * 7 ? ColourRed : ColourGreen;
  const conjureFrenzyCur = Math.min(
    (Game.cookies + GetWrinkConfigBank()) * 0.15,
    CacheNoGoldSwitchCookiesPS * 60 * 30,
  );
  const conjureFrenzyTime =
    Game.cookies + GetWrinkConfigBank() < CacheConjure * 7
      ? FormatTime((CacheConjure * 7 - (Game.cookies + GetWrinkConfigBank())) / GetCPS())
      : '';

  const conjureFrenzyReqFrag = document.createDocumentFragment();
  const conjureFrenzyReqSpan = document.createElement('span');
  conjureFrenzyReqSpan.style.fontWeight = 'bold';
  conjureFrenzyReqSpan.className = ColourTextPre + conjureFrenzyColour;
  conjureFrenzyReqSpan.textContent = Beautify_Beautify(CacheConjure * 7);
  conjureFrenzyReqFrag.appendChild(conjureFrenzyReqSpan);
  if (conjureFrenzyTime !== '') {
    const conjureFrenzyReqSmall = document.createElement('small');
    conjureFrenzyReqSmall.textContent = ` (${conjureFrenzyTime})`;
    conjureFrenzyReqFrag.appendChild(conjureFrenzyReqSmall);
  }
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Conjure Baked Goods" cookies required (frenzy)',
      conjureFrenzyReqFrag,
      'GoldCookTooltipPlaceholder',
    ),
  );
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Conjure Baked Goods" reward (max) (frenzy)',
      document.createTextNode(Beautify_Beautify(CacheConjureReward * 7)),
      'GoldCookTooltipPlaceholder',
    ),
  );
  section.appendChild(
    StatsListing(
      'withTooltip',
      '"Conjure Baked Goods" reward (cur)',
      document.createTextNode(Beautify_Beautify(conjureFrenzyCur)),
      'GoldCookTooltipPlaceholder',
    ),
  );
  if (CacheEdifice) {
    section.appendChild(
      StatsListing(
        'withTooltip',
        '"Spontaneous Edifice" cookies required (most expensive building)',
        document.createTextNode(`${Beautify_Beautify(CacheEdifice)} (${CacheEdificeBuilding})`),
        'GoldCookTooltipPlaceholder',
      ),
    );
  }

  const { minigame } = Game.Objects['Wizard tower'];
  const spellsCast = minigame.spellsCastTotal;
  const spellsNeeded = (function (val) {
    switch (true) {
      case val < 9:
        return 9 - val;
      case val < 99:
        return 99 - val;
      case val < 999:
        return 999 - val;
      default:
        return 'NA';
    }
  })(spellsCast);
  section.appendChild(
    StatsListing(
      'basic',
      'Spells cast',
      spellsCast < 999
        ? document.createTextNode(
            `Next achievement in ${spellsNeeded}, current total: ${Beautify_Beautify(spellsCast)}`,
          )
        : document.createTextNode(`No new achievement, current total: ${Beautify_Beautify(spellsCast)}`),
    ),
  );

  return section;
}

/**
 * This function creates the "Garden" section of the stats page
 * @returns	{object}	section		The object contating the Spells section
 */
function GardenSection() {
  const section = document.createElement('div');
  section.className = 'CMStatsGardenSection';

  const bakeberryColour = Game.cookies < Game.cookiesPs * 60 * 10 * 100 ? ColourRed : ColourGreen;
  const bakeberryFrag = document.createElement('span');
  bakeberryFrag.style.fontWeight = 'bold';
  bakeberryFrag.className = ColourTextPre + bakeberryColour;
  bakeberryFrag.textContent = Beautify_Beautify(Game.cookiesPs * 60 * 10 * 100);
  section.appendChild(
    StatsListing('basic', 'Cookies required for max reward of Bakeberry: ', bakeberryFrag),
  );

  const chocorootColour = Game.cookies < Game.cookiesPs * 60 * 100 ? ColourRed : ColourGreen;
  const chocorootFrag = document.createElement('span');
  chocorootFrag.style.fontWeight = 'bold';
  chocorootFrag.className = ColourTextPre + chocorootColour;
  chocorootFrag.textContent = Beautify_Beautify(Game.cookiesPs * 60 * 100);
  section.appendChild(
    StatsListing('basic', 'Cookies required for max reward of Chocoroot: ', chocorootFrag),
  );

  const queenbeetColour = Game.cookies < Game.cookiesPs * 60 * 60 * 25 ? ColourRed : ColourGreen;
  const queenbeetFrag = document.createElement('span');
  queenbeetFrag.style.fontWeight = 'bold';
  queenbeetFrag.className = ColourTextPre + queenbeetColour;
  queenbeetFrag.textContent = Beautify_Beautify(Game.cookiesPs * 60 * 60 * 25);
  section.appendChild(
    StatsListing('basic', 'Cookies required for max reward of Queenbeet: ', queenbeetFrag),
  );

  const duketaterColour = Game.cookies < Game.cookiesPs * 60 * 15 * 100 ? ColourRed : ColourGreen;
  const duketaterFrag = document.createElement('span');
  duketaterFrag.style.fontWeight = 'bold';
  duketaterFrag.className = ColourTextPre + duketaterColour;
  duketaterFrag.textContent = Beautify_Beautify(Game.cookiesPs * 60 * 15 * 100);
  section.appendChild(
    StatsListing('basic', 'Cookies required for max reward of Duketater: ', duketaterFrag),
  );
  const missingPlantDrops = [];
  Object.keys(PlantDrops).forEach((i) => {
    if (!Game.HasUnlocked(PlantDrops[i])) {
      missingPlantDrops.push(PlantDrops[i]);
    }
  });
  if (missingPlantDrops.length !== 0) {
    section.appendChild(
      StatsListing('basic', 'Rare plant drops left to unlock', StatsMissDisp(missingPlantDrops)),
    );
  }
  return section;
}

/**
 * This function creates the "Prestige" section of the stats page
 * @returns	{object}	section		The object contating the Prestige section
 */
function PrestigeSection() {
  const section = document.createElement('div');
  section.className = 'CMStatsPrestigeSection';

  const possiblePresMax = Math.floor(
    Game.HowMuchPrestige(
      CacheRealCookiesEarned +
        Game.cookiesReset +
        CacheWrinklersTotal +
        (Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg') ? CacheLastChoEgg : 0),
    ),
  );
  section.appendChild(
    StatsListing(
      'withTooltip',
      'Prestige level (cur / max)',
      document.createTextNode(`${Beautify_Beautify(Game.prestige)} / ${Beautify_Beautify(possiblePresMax)}`),
      'PrestMaxTooltipPlaceholder',
    ),
  );

  const neededCook = Math.max(
    0,
    Game.HowManyCookiesReset(possiblePresMax + 1) -
      (CacheRealCookiesEarned +
        Game.cookiesReset +
        CacheWrinklersTotal +
        (Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg') ? CacheLastChoEgg : 0)),
  );
  const cookiesNextFrag = document.createDocumentFragment();
  cookiesNextFrag.appendChild(document.createTextNode(Beautify_Beautify(neededCook)));
  const cookiesNextSmall = document.createElement('small');
  cookiesNextSmall.textContent = ` (${FormatTime(neededCook / CacheAvgCPSWithChoEgg, 1)})`;
  cookiesNextFrag.appendChild(cookiesNextSmall);
  section.appendChild(
    StatsListing(
      'withTooltip',
      'Cookies to next level',
      cookiesNextFrag,
      'NextPrestTooltipPlaceholder',
    ),
  );

  section.appendChild(
    StatsListing(
      'withTooltip',
      'Heavenly chips (cur / max)',
      document.createTextNode(
        `${Beautify_Beautify(Game.heavenlyChips)} / ${Beautify_Beautify(
          possiblePresMax - Game.prestige + Game.heavenlyChips,
        )}`,
      ),
      'HeavenChipMaxTooltipPlaceholder',
    ),
  );

  section.appendChild(
    StatsListing(
      'basic',
      'Heavenly chips per second (at current CPS)',
      document.createTextNode(Beautify_Beautify(CacheHCPerSecond, 2)),
    ),
  );

  const HCTarget = Number(
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.HeavenlyChipsTarget,
  );
  if (!Number.isNaN(HCTarget)) {
    const CookiesTillTarget =
      HCTarget - Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned));
    if (CookiesTillTarget > 0) {
      section.appendChild(
        StatsListing(
          'basic',
          'Heavenly chips to target set in settings (cur)',
          document.createTextNode(Beautify_Beautify(CookiesTillTarget)),
        ),
      );
      // Exact: cookies needed for the target level divided by CPS, not chips divided by the chip rate
      const cookiesForTarget =
        Game.HowManyCookiesReset(HCTarget) - (Game.cookiesReset + Game.cookiesEarned);
      section.appendChild(
        StatsListing(
          'basic',
          'Time till target (at current CPS)',
          document.createTextNode(FormatTime(cookiesForTarget / GetCPS())),
        ),
      );
    }
  }

  const resetBonus = ResetBonus(possiblePresMax);
  const resetFrag = document.createDocumentFragment();
  resetFrag.appendChild(document.createTextNode(Beautify_Beautify(resetBonus)));
  const increase = Math.round((resetBonus / Game.cookiesPs) * 10000);
  if (Number.isFinite(increase) && increase !== 0) {
    const resetSmall = document.createElement('small');
    resetSmall.textContent = ` (${increase / 100}% of income)`;
    resetFrag.appendChild(resetSmall);
  }
  section.appendChild(
    StatsListing('withTooltip', 'Reset bonus income', resetFrag, 'ResetTooltipPlaceholder'),
  );

  const currentPrestige = Math.floor(Game.HowMuchPrestige(Game.cookiesReset));
  const willHave = Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned));
  const willGet = willHave - currentPrestige;
  const { luckyDigit, luckyNumber, luckyPayout } = CalculateLuckyLevels(willHave);
  if (!Game.Has('Lucky digit')) {
    const luckyDigitDelta = luckyDigit - willHave;
    const luckyDigitReset = willGet + luckyDigitDelta;
    const fragLuckyDigit = document.createDocumentFragment();
    fragLuckyDigit.appendChild(
      document.createTextNode(
        `${luckyDigit.toLocaleString()} / ${luckyDigitReset.toLocaleString()} (+${luckyDigitDelta})`,
      ),
    );
    section.appendChild(
      StatsListing('basic', 'Next "Lucky Digit" (total / reset)', fragLuckyDigit),
    );
  }

  if (!Game.Has('Lucky number')) {
    const luckyNumberDelta = luckyNumber - willHave;
    const luckyNumberReset = willGet + luckyNumberDelta;
    const fragLuckyNumber = document.createDocumentFragment();
    fragLuckyNumber.appendChild(
      document.createTextNode(
        `${luckyNumber.toLocaleString()} / ${luckyNumberReset.toLocaleString()} (+${luckyNumberDelta})`,
      ),
    );
    section.appendChild(
      StatsListing('basic', 'Next "Lucky Number" (total / reset)', fragLuckyNumber),
    );
  }

  if (!Game.Has('Lucky payout')) {
    const luckyPayoutDelta = luckyPayout - willHave;
    const luckyPayoutReset = willGet + luckyPayoutDelta;
    const fragLuckyPayout = document.createDocumentFragment();
    fragLuckyPayout.appendChild(
      document.createTextNode(
        `${luckyPayout.toLocaleString()} / ${luckyPayoutReset.toLocaleString()} (+${luckyPayoutDelta})`,
      ),
    );
    section.appendChild(
      StatsListing('basic', 'Next "Lucky Payout" (total / reset)', fragLuckyPayout),
    );
  }

  return section;
}

/**
 * This function creates the "Season Specials" section of the stats page
 * @returns	{object}	section		The object contating the Season Specials section
 */
function SeasonSection() {
  const section = document.createElement('div');
  section.className = 'CMStatsSeasonSection';

  let specDisp = false;
  const missingHalloweenCookies = [];
  Object.keys(HalloCookies).forEach((i) => {
    if (!Game.Has(HalloCookies[i])) {
      missingHalloweenCookies.push(HalloCookies[i]);
      specDisp = true;
    }
  });
  const missingChristmasCookies = [];
  Object.keys(ChristCookies).forEach((i) => {
    if (!Game.Has(ChristCookies[i])) {
      missingChristmasCookies.push(ChristCookies[i]);
      specDisp = true;
    }
  });
  const missingValentineCookies = [];
  Object.keys(ValCookies).forEach((i) => {
    if (!Game.Has(ValCookies[i])) {
      missingValentineCookies.push(ValCookies[i]);
      specDisp = true;
    }
  });
  const missingNormalEggs = [];
  Object.keys(Game.eggDrops).forEach((i) => {
    if (!Game.HasUnlocked(Game.eggDrops[i])) {
      missingNormalEggs.push(Game.eggDrops[i]);
      specDisp = true;
    }
  });
  const missingRareEggs = [];
  Object.keys(Game.rareEggDrops).forEach((i) => {
    if (!Game.HasUnlocked(Game.rareEggDrops[i])) {
      missingRareEggs.push(Game.rareEggDrops[i]);
      specDisp = true;
    }
  });
  const choEgg = Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg');
  const centEgg = Game.Has('Century egg');

  if (Game.season === 'christmas' || specDisp || choEgg || centEgg) {
    section.appendChild(StatsHeader('Season Specials', 'Sea'));
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Sea) {
      if (missingHalloweenCookies.length !== 0) {
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Halloween cookies left to buy',
            StatsMissDisp(missingHalloweenCookies),
            Game.season === 'halloween',
          ),
        );
        let failRateHalloween = 0.95;
        if (Game.HasAchiev('Spooky cookies')) failRateHalloween = 0.8;
        if (Game.Has('Starterror')) failRateHalloween *= 0.9;
        failRateHalloween *= 1 / Game.dropRateMult();
        if (Game.hasGod) {
          const godLvl = Game.hasGod('seasons');
          if (godLvl === 1) failRateHalloween *= 0.9;
          else if (godLvl === 2) failRateHalloween *= 0.95;
          else if (godLvl === 3) failRateHalloween *= 0.97;
        }
        const obtainedCookiesChance = missingHalloweenCookies.length / 7;
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Chance of receiving a cookie from wrinkler/shiny wrinkler',
            document.createTextNode(
              `${Beautify_Beautify((1 - failRateHalloween) * obtainedCookiesChance * 100)}% / ${Beautify_Beautify(
                (1 - failRateHalloween * 0.9) * obtainedCookiesChance * 100,
              )}%`,
            ),
            Game.season === 'halloween',
          ),
        );
      }
      if (missingChristmasCookies.length !== 0) {
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Christmas cookies left to buy',
            StatsMissDisp(missingChristmasCookies),
            Game.season === 'christmas',
          ),
        );
        let failRateChristmas = 0.8;
        if (Game.HasAchiev('Let it snow')) failRateChristmas = 0.6;
        failRateChristmas *= 1 / Game.dropRateMult();
        if (Game.Has('Starsnow')) failRateChristmas *= 0.95;
        if (Game.hasGod) {
          const godLvl = Game.hasGod('seasons');
          if (godLvl === 1) failRateChristmas *= 0.9;
          else if (godLvl === 2) failRateChristmas *= 0.95;
          else if (godLvl === 3) failRateChristmas *= 0.97;
        }
        const obtainedCookiesChance = missingChristmasCookies.length / 7;
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Chance of receiving a cookie from reindeer',
            document.createTextNode(
              `${Beautify_Beautify((1 - failRateChristmas) * obtainedCookiesChance * 100)}%`,
            ),
            Game.season === 'christmas',
          ),
        );
      }
      if (missingValentineCookies.length !== 0) {
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Valentine cookies left to buy',
            StatsMissDisp(missingValentineCookies),
            Game.season === 'valentines',
          ),
        );
      }
      const dropRateEgg = function (StartingFailRate) {
        let failRateEgg = StartingFailRate * (1 / Game.dropRateMult());
        if (Game.HasAchiev('Hide & seek champion')) failRateEgg *= 0.7;
        if (Game.Has('Omelette')) failRateEgg *= 0.9;
        if (Game.Has('Starspawn')) failRateEgg *= 0.9;
        if (Game.hasGod) {
          const godLvl = Game.hasGod('seasons');
          if (godLvl === 1) failRateEgg *= 0.9;
          else if (godLvl === 2) failRateEgg *= 0.95;
          else if (godLvl === 3) failRateEgg *= 0.97;
        }
        // Calculations courtesy of @svschouw, at https://github.com/Aktanusa/CookieMonster/issues/25
        const succesRateEgg = 1 - failRateEgg;
        const obtainedEggs = Game.eggDrops.length - missingNormalEggs.length;
        const obtainedRareEggs = Game.rareEggDrops.length - missingRareEggs.length;
        const pNormal1 = succesRateEgg * 0.9 * (1 - obtainedEggs / Game.eggDrops.length);
        const pRare1 = succesRateEgg * 0.1 * (1 - obtainedRareEggs / Game.rareEggDrops.length);
        const pRedropNormal = succesRateEgg * 0.9 * (obtainedEggs / Game.eggDrops.length);
        const pRedropRare = succesRateEgg * 0.1 * (obtainedRareEggs / Game.rareEggDrops.length);
        const pRedrop = pRedropNormal + pRedropRare;
        const pNormal2 = pRedrop * 0.9 * (1 - obtainedEggs / Game.eggDrops.length);
        const pRare2 = pRedrop * 0.1 * (1 - obtainedRareEggs / Game.rareEggDrops.length);
        return [pNormal1 + pNormal2, pRare1 + pRare2];
      };
      if (missingNormalEggs.length !== 0) {
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Normal easter eggs left to unlock',
            StatsMissDisp(missingNormalEggs),
            Game.season === 'easter',
          ),
        );
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Chance of receiving an egg from wrinkler/golden cookie',
            document.createTextNode(
              `${Beautify_Beautify(dropRateEgg(0.98)[0] * 100)}% / ${Beautify_Beautify(dropRateEgg(0.9)[0] * 100)}%`,
            ),
            Game.season === 'easter',
          ),
        );
      }
      if (missingRareEggs.length !== 0) {
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Rare easter eggs left to unlock',
            StatsMissDisp(missingRareEggs),
            Game.season === 'easter',
          ),
        );
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Chance of receiving a rare egg from wrinkler/golden cookie',
            document.createTextNode(
              `${Beautify_Beautify(dropRateEgg(0.98)[1] * 100)}% / ${Beautify_Beautify(dropRateEgg(0.9)[1] * 100)}%`,
            ),
            Game.season === 'easter',
          ),
        );
      }

      if (Game.season === 'christmas')
        section.appendChild(
          StatsMissDispListing(
            'basic',
            'Reindeer reward',
            document.createTextNode(Beautify_Beautify(CacheSeaSpec)),
            true,
          ),
        );
      if (choEgg) {
        section.appendChild(
          StatsListing(
            'withTooltip',
            'Chocolate egg cookies',
            document.createTextNode(Beautify_Beautify(CacheLastChoEgg)),
            'ChoEggTooltipPlaceholder',
          ),
        );
      }
      if (centEgg) {
        section.appendChild(
          StatsListing(
            'basic',
            'Century egg multiplier',
            document.createTextNode(`${Math.round((CacheCentEgg - 1) * 10000) / 100}%`),
          ),
        );
      }
    }
  }
  return section;
}

;// ./src/Disp/MenuSections/Statistics/CreateMissingAchievements.js
function CrateTooltipLockedAchievements(me) {
  const tags = [];
  if (me.pool === 'shadow') tags.push('Shadow Achievement', '#9700cf');
  else tags.push('Achievement', 0);
  tags.push('Locked', 0);

  let neuromancy = 0;
  if (Game.Has('Neuromancy') || (Game.sesame && me.pool === 'debug')) neuromancy = 1;
  if (neuromancy && me.won === 0) tags.push('Click to win!', '#00c462');
  else if (neuromancy && me.won > 0) tags.push('Click to lose!', '#00c462');

  let { icon } = me;
  if (me.iconFunction) icon = me.iconFunction();

  let { desc } = me;
  if (me.descFunc) desc = me.descFunc('stats');

  let tagsStr = '';
  for (let i = 0; i < tags.length; i += 2) {
    if (i % 2 === 0)
      tagsStr += ` <div class="tag" style="color:${tags[i + 1] === 0 ? '#fff' : tags[i + 1]};">[${
        tags[i]
      }]</div>`;
  }
  tagsStr = tagsStr.substring(1);

  return `<div style="padding:8px 4px;min-width:350px;opacity:0.5">
  <div class="icon" style="float:left;margin-left:-8px;margin-top:-8px;background-position:${
    -icon[0] * 48
  }px ${-icon[1] * 48}px;"></div>
  <div class="name">${me.name}</div>
  ${tagsStr}<div class="line"></div><div class="description">${desc}</div></div>
  ${
    Game.sesame
      ? `<div style="font-size:9px;">Id : ${me.id} | Order : ${Math.floor(me.order)}${
          me.tier ? ` | Tier : ${me.tier}` : ''
        }</div>`
      : ''
  }`;
}

/**
 * This function overwrites the crates of missing achievements
 */
function AddMissingAchievements() {
  let achievs;
  Object.values(document.querySelectorAll('div.title')).forEach((i) => {
    if (i.textContent.includes('Achievements')) {
      achievs = i.parentElement.querySelectorAll('div.listing.crateBox')[0];
    }
  });
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.MissingAchievements) {
    Object.values(achievs.children).forEach((achievsCrate) => {
      if (!achievsCrate.className.includes('enabled')) {
        const id = achievsCrate.onclick.toString().split(/\[(.*)\]/gi)[1];
        const { icon } = Game.AchievementsById[id];
        // eslint-disable-next-line no-param-reassign
        achievsCrate.style.backgroundPosition = `${-icon[0] * 48}px ${-icon[1] * 48}px`;
        // eslint-disable-next-line no-param-reassign
        achievsCrate.onmouseover = function () {
          if (!Game.mouseDown) {
            Game.setOnCrate(this);
            Game.tooltip.dynamic = 1;
            Game.tooltip.draw(
              this,
              () =>
                (function () {
                  return CrateTooltipLockedAchievements(Game.AchievementsById[id]);
                })(),
              'top',
            );
            Game.tooltip.wobble();
          }
        };
      }
    });
  }
}

;// ./src/Disp/MenuSections/Statistics/AscensionSection.js
/** Creates the "Ascension Advisor" section of the statistics page */








/**
 * Creates a horizontal meter
 * @param	{number}	fraction	Filled fraction (0 to 1)
 * @param	{string}	colour		Colour name used by Cookie Monster colour classes
 * @param	{string}	label		Text drawn over the meter
 * @returns	{object}	div			The meter
 */
function CreateMeter(fraction, colour, label) {
  const meter = document.createElement('div');
  meter.className = 'CMMeter';
  const fill = document.createElement('div');
  fill.className = `CMMeterFill ${ColourBackPre}${colour}`;
  fill.style.width = `${Math.round(Math.min(Math.max(fraction, 0), 1) * 1000) / 10}%`;
  meter.appendChild(fill);
  const text = document.createElement('div');
  text.className = 'CMMeterLabel';
  text.textContent = label;
  meter.appendChild(text);
  return meter;
}

/**
 * Creates the round "?" that shows one of the simple tooltips on hover
 * @param	{string}	placeholder	The id of the tooltip in SimpleTooltipElements
 * @returns	{object}	span
 */
function CreateHelpBubble(placeholder) {
  const bubble = document.createElement('span');
  bubble.className = 'CMHelpBubble';
  bubble.textContent = '?';
  bubble.onmouseout = function () {
    Game.tooltip.hide();
  };
  bubble.onmouseover = function () {
    Game.tooltip.draw(this, escape(SimpleTooltipElements[placeholder].innerHTML));
  };
  return bubble;
}

/**
 * This function creates the "Ascension Advisor" section of the stats page
 * @returns	{object}	section		The object containing the section
 */
function AscensionSection() {
  const summary = AscensionSummary();

  const section = document.createElement('div');
  section.className = 'CMStatsAscensionSection CMAdvisor';

  const headline = document.createElement('div');
  headline.className = `CMAdvisorHeadline ${ColourTextPre}${summary.colour}`;
  headline.appendChild(document.createTextNode(`${summary.headline} `));
  headline.appendChild(CreateHelpBubble('AscendAdvisorTooltipPlaceholder'));
  section.appendChild(headline);
  if (summary.status === 'na' || summary.status === 'early') return section;

  if (summary.status !== 'none') {
    section.appendChild(
      CreateMeter(
        summary.readiness,
        summary.colour,
        summary.status === 'ready'
          ? 'Optimal point reached'
          : `${FormatPercent(summary.readiness * 100)} of the optimal run completed`,
      ),
    );
  }

  const grid = document.createElement('div');
  grid.className = 'CMAdvisorGrid';
  const row = (label, value) => {
    const name = document.createElement('div');
    name.className = 'CMAdvisorLabel';
    name.textContent = label;
    grid.appendChild(name);
    const content = document.createElement('div');
    content.textContent = value;
    grid.appendChild(content);
  };
  row(
    'Ascending now',
    `+${Beautify_Beautify(summary.levelsNow)} prestige level${summary.levelsNow === 1 ? '' : 's'}, +${FormatPercent(
      summary.speedGainNow * 100,
    )} production in every future run`,
  );
  if (summary.status === 'wait') {
    row(
      'At the optimum',
      `+${Beautify_Beautify(summary.levelsAtTarget)} prestige levels, +${FormatPercent(
        summary.speedGainAtTarget * 100,
      )} production`,
    );
    if (summary.costOfAscendingNow !== null)
      row(
        'Ascending early costs',
        `≈ ${ShortDuration(summary.costOfAscendingNow)} of total progress`,
      );
  }
  row('This run', `${ShortDuration(summary.runTime)} long, cookies baked growing like time`);
  const exponent = document.createElement('sup');
  exponent.textContent = summary.beta.toFixed(1);
  grid.lastChild.appendChild(exponent);
  section.appendChild(grid);

  const checklist = [];
  if (CacheWrinklersTotal > 0)
    checklist.push(
      `Pop all wrinklers before ascending (+${Beautify_Beautify(CacheWrinklersTotal)} cookies)`,
    );
  if (Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg'))
    checklist.push(
      `Buy the Chocolate egg right before ascending (+${Beautify_Beautify(CacheLastChoEgg)} cookies)`,
    );
  // Heavenly chips: what ascending now would buy along the purchase order, and what comes next
  const order = AscensionCache.heavenlyOrder;
  let chips = Game.heavenlyChips + Math.max(0, summary.levelsNow);
  const buys = [];
  if (!Game.Upgrades.Legacy.bought && chips >= 1) {
    buys.push('Legacy');
    chips -= 1;
  }
  let index = 0;
  while (index < order.length && order[index].cost <= chips) {
    buys.push(order[index].name);
    chips -= order[index].cost;
    index += 1;
  }
  if (buys.length > 0)
    checklist.push(
      `Ascending now buys ${buys.slice(0, 4).join(', ')}${
        buys.length > 4 ? ` and ${buys.length - 4} more` : ''
      } with heavenly chips`,
    );
  if (index < order.length)
    checklist.push(
      `Next heavenly upgrade: ${order[index].name} (${Beautify_Beautify(order[index].cost)} chips${
        order[index].bundle.length > 1 ? ' with its parents' : ''
      }, +${FormatPercent((order[index].mult - 1) * 100)} production)`,
    );
  if (checklist.length > 0) {
    const list = document.createElement('ul');
    list.className = 'CMChecklist';
    checklist.forEach((item) => {
      const li = document.createElement('li');
      li.textContent = item;
      list.appendChild(li);
    });
    section.appendChild(list);
  }
  return section;
}

;// ./src/Disp/MenuSections/Statistics/AddStatsPage.js
/** Main function to create the sections of Cookie Monster on the Statistics page */














/**
 * This function adds stats created by CookieMonster to the stats page
 * It is called by CM.Disp.AddMenu
 * @param {object} title	On object that includes the title of the menu
 */
function AddMenuStats(title) {
  const stats = document.createElement('div');
  stats.className = 'subsection';
  stats.appendChild(title);

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AscendAdvisor) {
    stats.appendChild(StatsHeader('Ascension Advisor', 'Ascension'));
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Ascension) {
      stats.appendChild(AscensionSection());
    }
  }

  stats.appendChild(StatsHeader('Lucky Cookies', 'Lucky'));
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Lucky) {
    stats.appendChild(LuckySection());
  }

  stats.appendChild(StatsHeader('Chain Cookies', 'Chain'));
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Chain) {
    stats.appendChild(ChainSection());
  }

  if (Game.Objects['Wizard tower'].minigameLoaded) {
    stats.appendChild(StatsHeader('Spells', 'Spells'));
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Spells) {
      stats.appendChild(SpellsSection());
    }
  }

  if (Game.Objects.Farm.minigameLoaded) {
    stats.appendChild(StatsHeader('Garden', 'Garden'));
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Garden) {
      stats.appendChild(GardenSection());
    }
  }

  stats.appendChild(StatsHeader('Prestige', 'Prestige'));
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Prestige) {
    stats.appendChild(PrestigeSection());
  }

  if (Game.cpsSucked > 0) {
    stats.appendChild(StatsHeader('Wrinklers', 'Wrink'));
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Wrink) {
      const popAllFrag = document.createDocumentFragment();
      popAllFrag.appendChild(
        document.createTextNode(
          `${Beautify_Beautify(CacheWrinklersTotal)} / ${Beautify_Beautify(CacheWrinklersNormal)} `,
        ),
      );
      const popAllA = document.createElement('a');
      popAllA.textContent = 'Pop All Normal';
      popAllA.className = 'option';
      popAllA.onclick = function () {
        PopAllNormalWrinklers();
      };
      popAllFrag.appendChild(popAllA);
      stats.appendChild(
        StatsListing('basic', 'Rewards of Popping (All/Normal)', popAllFrag),
      );
      const popFattestFrag = document.createDocumentFragment();
      popFattestFrag.appendChild(document.createTextNode(`${Beautify_Beautify(CacheWrinklersFattest[0])} `));
      const popFattestA = document.createElement('a');
      popFattestA.textContent = 'Pop Single Fattest';
      popFattestA.className = 'option';
      popFattestA.onclick = function () {
        if (CacheWrinklersFattest[1] !== null) Game.wrinklers[CacheWrinklersFattest[1]].hp = 0;
      };
      popFattestFrag.appendChild(popFattestA);
      stats.appendChild(
        StatsListing(
          'basic',
          `Rewards of Popping Single Fattest Non-Shiny Wrinkler (id: ${
            CacheWrinklersFattest[1] !== null ? CacheWrinklersFattest[1] : 'None'
          })`,
          popFattestFrag,
        ),
      );
    }
  }

  stats.appendChild(SeasonSection());

  stats.appendChild(StatsHeader('Achievements', 'Achievs'));
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Achievs) {
    Object.keys(Game.Objects).forEach((i) => {
      const ObjectsTillNext = CacheObjectsNextAchievement[i];
      stats.appendChild(
        StatsListing(
          'basic',
          i,
          ObjectsTillNext.AmountNeeded < 101
            ? document.createTextNode(
                `Next achievement in ${ObjectsTillNext.AmountNeeded}, price: ${Beautify_Beautify(
                  ObjectsTillNext.price,
                )}`,
              )
            : document.createTextNode('No new achievement for next 100 buildings'),
        ),
      );
    });
  }

  stats.appendChild(StatsHeader('Miscellaneous', 'Misc'));
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.headers.Misc) {
    stats.appendChild(
      StatsListing(
        'basic',
        `Average cookies per second (past ${
          CookieTimes[
            Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgCPSHist
          ] < 60
            ? `${
                CookieTimes[
                  Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgCPSHist
                ]
              } seconds`
            : CookieTimes[
                Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgCPSHist
              ] /
                60 +
              (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgCPSHist === 3
                ? ' minute'
                : ' minutes')
        })`,
        document.createTextNode(Beautify_Beautify(GetCPS(), 3)),
      ),
    );
    stats.appendChild(
      StatsListing(
        'basic',
        `Average cookie clicks per second (past ${
          ClickTimes[
            Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgClicksHist
          ]
        }${
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgClicksHist === 0
            ? ' second'
            : ' seconds'
        })`,
        document.createTextNode(Beautify_Beautify(CacheAverageClicks, 1)),
      ),
    );
    stats.appendChild(
      StatsListing(
        'basic',
        `Cookies from clicking (past ${
          ClickTimes[
            Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgClicksHist
          ]
        }${
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgClicksHist === 0
            ? ' second'
            : ' seconds'
        })`,
        document.createTextNode(
          Beautify_Beautify(
            CacheAverageCookiesFromClicks.calcSum(
              CacheAverageClicks *
                ClickTimes[
                  Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AvgClicksHist
                ],
            ),
          ),
        ),
      ),
    );
    if (Game.Has('Fortune cookies')) {
      const fortunes = [];
      Object.keys(Fortunes).forEach((i) => {
        if (!Game.Has(Fortunes[i])) {
          fortunes.push(Fortunes[i]);
        }
      });
      if (fortunes.length !== 0)
        stats.appendChild(
          StatsListing(
            'basic',
            'Fortune Upgrades Left to Buy',
            StatsMissDisp(fortunes),
          ),
        );
    }
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ShowMissedGC) {
      stats.appendChild(
        StatsListing(
          'basic',
          'Missed golden cookies',
          document.createTextNode(Beautify_Beautify(Game.missedGoldenClicks)),
        ),
      );
    }
    if (Game.prefs.autosave) {
      const timer = document.createElement('span');
      timer.id = 'CMStatsAutosaveTimer';
      timer.innerText = Game.sayTime(
        Game.fps * 60 - (Game.OnAscend ? 0 : Game.T % (Game.fps * 60)),
        4,
      );
      stats.appendChild(StatsListing('basic', 'Time till autosave', timer));
    }
  }

  l('menu').insertBefore(stats, l('menu').childNodes[2]);

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.MissingUpgrades) {
    AddMissingUpgrades();
  }
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.MissingAchievements) {
    AddMissingAchievements();
  }
}

;// ./src/Disp/MenuSections/AddMenus.js



/**
 * This function adds the calll the functions to add extra info to the stats and options pages
 */
function AddMenu() {
  const title = document.createElement('div');
  title.className = 'title';

  if (Game.onMenu === 'stats') {
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Stats) {
      title.textContent = 'Cookie Monster Statistics';
      AddMenuStats(title);
    }
  } else if (Game.onMenu === 'prefs') {
    // Added because Framework is broken
    l('menu').childNodes[2].insertBefore(
      createMenuOptions(),
      l('menu').childNodes[2].childNodes[l('menu').childNodes[2].childNodes.length - 1],
    );
  }
}

;// ./src/Disp/TabTitle/TabTitle.js
/** Functions related to updating the tab in the browser's tab-bar */






/**
 * This function updates the tab title
 * It is called on every loop by Game.Logic() which also sets CM.Disp.Title to Game.cookies
 */
function UpdateTitle() {
  if (
    Game.OnAscend ||
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Title === 0
  ) {
    document.title = Title;
  } else if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Title === 1) {
    let addFC = false;
    let addSP = false;
    let titleGC;
    let titleFC;
    let titleSP;

    if (CacheSpawnedGoldenShimmer) {
      if (CacheSpawnedGoldenShimmer.wrath)
        titleGC = `[W${Math.ceil(CacheSpawnedGoldenShimmer.life / Game.fps)}]`;
      else titleGC = `[G${Math.ceil(CacheSpawnedGoldenShimmer.life / Game.fps)}]`;
    } else if (!Game.Has('Golden switch [off]')) {
      titleGC = `[${Number(l('CMTimerBarGCMinBar').textContent) < 0 ? '!' : ''}${Math.ceil(
        (Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.time) / Game.fps,
      )}]`;
    } else titleGC = '[GS]';

    if (LastTickerFortuneState) {
      addFC = true;
      titleFC = '[F]';
    }

    if (Game.season === 'christmas') {
      addSP = true;
      if (LastSeasonPopupState) titleSP = `[R${Math.ceil(CacheSeasonPopShimmer.life / Game.fps)}]`;
      else {
        titleSP = `[${Number(l('CMTimerBarRenMinBar').textContent) < 0 ? '!' : ''}${Math.ceil(
          (Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.time) / Game.fps,
        )}]`;
      }
    }

    // Remove previous timers and add current cookies
    let str = Title;
    if (str.charAt(0) === '[') {
      str = str.substring(str.lastIndexOf(']') + 1);
    }
    document.title = `${titleGC + (addFC ? titleFC : '') + (addSP ? titleSP : '')} ${str}`;
  } else if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.Title === 2) {
    let str = '';
    let spawn = false;
    if (CacheSpawnedGoldenShimmer) {
      spawn = true;
      if (CacheSpawnedGoldenShimmer.wrath)
        str += `[W${Math.ceil(CacheSpawnedGoldenShimmer.life / Game.fps)}]`;
      else str += `[G${Math.ceil(CacheSpawnedGoldenShimmer.life / Game.fps)}]`;
    }
    if (LastTickerFortuneState) {
      spawn = true;
      str += '[F]';
    }
    if (Game.season === 'christmas' && LastSeasonPopupState) {
      str += `[R${Math.ceil(CacheSeasonPopShimmer.life / Game.fps)}]`;
      spawn = true;
    }
    if (spawn) str += ' - ';
    let title = 'Cookie Clicker';
    if (Game.season === 'fools') title = 'Cookie Baker';
    str += title;
    document.title = str;
  }
}

;// ./src/Disp/Tooltips/AscendButton.js





/**
 * This function replaces the tooltip of the ascend button
 */
function ReplaceAscendTooltip() {
  const cookiesToNext = Math.max(
    0,
    Game.HowManyCookiesReset(
      Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned)) + 1,
    ) -
      (Game.cookiesEarned + Game.cookiesReset),
  );

  const startDate = Game.sayTime(((Date.now() - Game.startDate) / 1000) * Game.fps, -1);
  let str = `You've been on this run for <b>${
    startDate === '' ? 'not very long' : startDate
  }</b>.<br>
  <div class="line"></div>`;
  if (Game.prestige > 0) {
    str += `Your prestige level is currently <b>${Beautify_Beautify(Game.prestige)}</b>.<br>(CpS +${Beautify_Beautify(
      Game.prestige,
    )}%)
    <div class="line"></div>`;
  }
  if (CacheLastHeavenlyChips < 1) str += 'Ascending now would grant you no prestige.';
  else if (CacheLastHeavenlyChips < 2)
    str +=
      'Ascending now would grant you<br><b>1 prestige level</b> (+1% CpS)<br>and <b>1 heavenly chip</b> to spend.';
  else
    str += `Ascending now would grant you<br><b>${Beautify_Beautify(
      CacheLastHeavenlyChips,
    )} prestige levels</b> (+${Beautify_Beautify(CacheLastHeavenlyChips)}% CpS)<br>and <b>${Beautify_Beautify(
      CacheLastHeavenlyChips,
    )} heavenly chips</b> to spend.`;
  str += `<div class="line"></div>
  You need <b>${Beautify_Beautify(cookiesToNext)} more cookies</b> for the next level.<br>
  ${
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipAscendButton
      ? `<div class='line'></div>It takes ${CacheTimeTillNextPrestige} to reach the next level and you are making ${Beautify_Beautify(
          CacheHCPerSecond,
          2,
        )} chips per second.<br>`
      : ''
  }`;

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AscendAdvisor) {
    const summary = AscensionSummary();
    if (summary.status !== 'na' && summary.status !== 'early') {
      str += `<div class="line"></div><b class="${ColourTextPre}${summary.colour}">${summary.headline}</b>`;
      if (summary.status === 'wait')
        str += `<br>Waiting for <b>+${Beautify_Beautify(summary.levelsAtTarget)} levels</b> (+${FormatPercent(
          summary.speedGainAtTarget * 100,
        )} production) instead of ascending now for +${FormatPercent(summary.speedGainNow * 100)}.`;
    }
  }
  l('ascendTooltip').innerHTML = str;
}

;// ./src/Disp/Tooltips/PositionLocation.js
/**
 * This function updates the location of the tooltip
 * It is called by Game.tooltip.update() because of CM.Main.ReplaceNative()
 */
function UpdateTooltipLocation() {
  if (Game.tooltip.origin === 'store') {
    let warnOffset = 0;
    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnLucky === 1 &&
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnPos === 1 &&
      l('CMDispTooltipWarningParent') !== null
    ) {
      warnOffset = l('CMDispTooltipWarningParent').clientHeight - 4;
    }
    Game.tooltip.tta.style.top = `${Math.min(
      parseInt(Game.tooltip.tta.style.top, 10),
      l('game').clientHeight +
        l('topBar').clientHeight -
        Game.tooltip.tt.clientHeight -
        warnOffset -
        46,
    )}px`;
  }
  // Kept for future possible use if the code changes again
  /* else if (!Game.onCrate && !Game.OnAscend && CM.Options.TimerBar === 1 && CM.Options.TimerBarPos === 0) {
		Game.tooltip.tta.style.top = (parseInt(Game.tooltip.tta.style.top) + parseInt(CM.Disp.TimerBar.style.height)) + 'px';
	} */
}

;// ./src/Main/ReplaceGameElements/TooltipUpgrades.js



/**
 * This function replaces the original .onmouseover functions of upgrades so that it calls CM.Disp.Tooltip()
 * CM.Disp.Tooltip() sets the tooltip type to 'u'
 * It is called by Game.RebuildUpgrades() through CM.Main.ReplaceNative() and is therefore not permanent like the other ReplaceTooltip functions
 */
function ReplaceTooltipUpgrade() {
  TooltipUpgradeBackup = [];
  Object.keys(Game.UpgradesInStore).forEach((i) => {
    if (l(`upgrade${i}`).onmouseover !== null) {
      TooltipUpgradeBackup[i] = l(`upgrade${i}`).onmouseover;
      l(`upgrade${i}`).onmouseover = function () {
        if (!Game.mouseDown) {
          Game.setOnCrate(this);
          Game.tooltip.dynamic = 1;
          Game.tooltip.draw(this, () => CreateTooltip('u', `${i}`), 'store');
          Game.tooltip.wobble();
        }
      };
    }
  });
}

;// ./src/Main/ReplaceGameFunctions/FixMouse.js
/**
 * This function fixes Game.mouseY as a result of bars that are added by CookieMonster
 * It is called by Game.UpdateWrinklers(), Game.UpdateSpecial() and the .onmousover of the BigCookie
 * before execution of their actual function
 */
function FixMouseY(target) {
  if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1 &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarPos === 0
  ) {
    const timerBarHeight = parseInt(l('CMTimerBar').style.height, 10);
    Game.mouseY -= timerBarHeight;
    target();
    Game.mouseY += timerBarHeight;
  } else {
    target();
  }
}

;// ./src/Main/ReplaceGameFunctions/ReplaceNative.js









 // eslint-disable-line no-unused-vars
 // eslint-disable-line no-unused-vars




/**
 * This function replaces certain native (from the base-game) functions
 */
function ReplaceNative() {
  // eslint-disable-next-line no-undef
  BackupFunctions.Beautify = Beautify;
  // eslint-disable-next-line no-undef
  Beautify = Beautify_Beautify;

  BackupFunctions.CalculateGains = Game.CalculateGains;
  Game.CalculateGains = function () {
    BackupFunctions.CalculateGains();
    SimDoSims = 1;
    CycliusDateAtBeginLoop = Date.now();
    CenturyDateAtBeginLoop = Date.now();
  };

  BackupFunctions.tooltip = {};
  BackupFunctions.tooltip.draw = Game.tooltip.draw;
  BackupFunctions.tooltip.drawMod = new Function( // eslint-disable-line no-new-func
    `return ${Game.tooltip.draw.toString().split('this').join('Game.tooltip')}`,
  )();
  Game.tooltip.draw = function (from, text, origin) {
    BackupFunctions.tooltip.drawMod(from, text, origin);
  };

  BackupFunctions.tooltip.update = Game.tooltip.update;
  BackupFunctions.tooltip.updateMod = new Function( // eslint-disable-line no-new-func
    `return ${Game.tooltip.update.toString().split('this.').join('Game.tooltip.')}`,
  )();
  Game.tooltip.update = function () {
    BackupFunctions.tooltip.updateMod();
    UpdateTooltipLocation();
  };

  BackupFunctions.UpdateWrinklers = Game.UpdateWrinklers;
  Game.UpdateWrinklers = function () {
    FixMouseY(BackupFunctions.UpdateWrinklers);
  };

  BackupFunctions.UpdateSpecial = Game.UpdateSpecial;
  Game.UpdateSpecial = function () {
    FixMouseY(BackupFunctions.UpdateSpecial);
  };

  // Assumes newer browsers
  l('bigCookie').removeEventListener('click', Game.ClickCookie, false);
  l('bigCookie').addEventListener(
    'click',
    (event) => {
      FixMouseY(() => Game.ClickCookie(event, 0));
    },
    false,
  );

  BackupFunctions.RebuildUpgrades = Game.RebuildUpgrades;
  Game.RebuildUpgrades = function () {
    BackupFunctions.RebuildUpgrades();
    ReplaceTooltipUpgrade();
    Game.CalculateGains();
  };

  BackupFunctions.ClickProduct = Game.ClickProduct;
  /**
   * This function adds a check to the purchase of a building to allow BulkBuyBlock to work.
   * If the options is 1 (on) bulkPrice is under cookies you can't buy the building.
   */
  Game.ClickProduct = function (what) {
    if (
      !Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BulkBuyBlock ||
      Game.ObjectsById[what].bulkPrice <= Game.cookies ||
      Game.buyMode === -1
    ) {
      BackupFunctions.ClickProduct(what);
    }
  };

  BackupFunctions.DescribeDragonAura = Game.DescribeDragonAura;
  /**
   * This function adds the function CM.Disp.AddAuraInfo() to Game.DescribeDragonAura()
   * This adds information about CPS differences and costs to the aura choosing interface
   * @param	{number}	aura	The number of the aura currently selected by the mouse/user
   */
  Game.DescribeDragonAura = function (aura) {
    BackupFunctions.DescribeDragonAura(aura);
    AddAuraInfo(aura);
  };

  BackupFunctions.ToggleSpecialMenu = Game.ToggleSpecialMenu;
  /**
   * This function adds the code to display the tooltips for the levelUp button of the dragon
   */
  Game.ToggleSpecialMenu = function (on) {
    BackupFunctions.ToggleSpecialMenu(on);
    AddDragonLevelUpTooltip();
  };

  BackupFunctions.UpdateMenu = Game.UpdateMenu;
  Game.UpdateMenu = function () {
    if (typeof jscolor.picker === 'undefined' || typeof jscolor.picker.owner === 'undefined') {
      BackupFunctions.UpdateMenu();
      AddMenu();
    }
  };

  BackupFunctions.sayTime = Game.sayTime;

  CMSayTime = function (time, detail) {
    if (Number.isNaN(time) || time <= 0) return BackupFunctions.sayTime(time, detail);
    return FormatTime(time / Game.fps, 1);
  };

  BackupFunctions.Logic = Game.Logic;
  Game.Logic = function () {
    BackupFunctions.Logic();

    // Update tab title
    let title = 'Cookie Clicker';
    if (Game.season === 'fools') title = 'Cookie Baker';

    Title = `${Game.OnAscend ? 'Ascending! ' : ''}${Beautify_Beautify(Game.cookies)} ${
      Game.cookies === 1 ? 'cookie' : 'cookies'
    } - ${title}`;
    UpdateTitle();

    // Since the Ascend Tooltip is not actually a tooltip we need to add our additional info here...
    ReplaceAscendTooltip();
  };
}

;// ./src/Main/WrinklerArea/AddDetectArea.js
 // eslint-disable-line no-unused-vars

/**
 * This function creates .onmouseover/out events that determine if the mouse is hovering-over a Wrinkler
 * As wrinklers are not appended to the DOM we us a different system than for other tooltips
 */
function AddWrinklerAreaDetect() {
  l('backgroundLeftCanvas').onmouseover = function () {
    TooltipWrinklerArea = 1;
  };
  l('backgroundLeftCanvas').onmouseout = function () {
    TooltipWrinklerArea = 0;
    Game.tooltip.hide();
    Object.keys(Game.wrinklers).forEach((i) => {
      TooltipWrinklerBeingShown[i] = 0;
    });
  };
}

;// ./src/Disp/buildingTiles/toggleBuildingLock.js
/**
 * This function toggle the locked state of a building
 * @param	{number}	index	Index of the row to change
 */
function toggleBuildingLock(index) {
  if (l(`productLock${index}`).innerHTML === 'Lock') {
    // Add to storing array
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames.push(
      index.toString(),
    );

    // Update styles
    l(`row${index}`).style.pointerEvents = 'none';
    l(`row${index}`).style.opacity = '0.4';
    l(`productLock${index}`).innerHTML = 'Unlock';
    l(`productLock${index}`).style.pointerEvents = 'auto';
  } else {
    // Remove from storing array
    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames.includes(
        index.toString(),
      )
    ) {
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames =
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames.filter(
          (value) => value !== index.toString(),
        );
    }

    // Update styles
    l(`productLock${index}`).innerHTML = 'Lock';
    l(`row${index}`).style.pointerEvents = 'auto';
    l(`row${index}`).style.opacity = '1';
  }
}

;// ./src/Disp/buildingTiles/createBuildingLockButtons.js


/**
 * This function adds a lock button to the "building view" in the middle section
 */
function createBuildingLockButtons() {
  Object.keys(l('rows').children).forEach((index) => {
    const productButtons = l('rows').children[index].children[1];
    const button = document.createElement('div');
    button.id = `productLock${Number(index) + 1}`;
    button.className = 'productButton';
    button.innerHTML = 'Lock';
    button.onclick = function () {
      toggleBuildingLock(Number(index) + 1);
    };
    productButtons.appendChild(button);
  });
}

;// ./src/Main/Initialization.js












 // eslint-disable-line no-unused-vars




 // eslint-disable-line no-unused-vars


// import createMenuInfo from '../Disp/MenuSections/createMenuInfo.js';


/**
 * Initialization loop of Cookie Monster
 */
function InitializeCookieMonster() {
  // Create global data object
  window.CookieMonsterData = {};

  // Register listeners in Cookie Monster Mod Framework
  // Commented because Framework is currently broken
  // Game.mods.cookieMonsterFramework.listeners.infoMenu.push(createMenuInfo);
  Game.mods.cookieMonsterFramework.listeners.optionsMenu.push(createMenuOptions);

  InitData();
  CacheStatsCookies();
  InitCache();

  // Stored to check if we need to re-initiliaze data
  LastModCount = Object.keys(Game.mods).length;

  // Creating visual elements
  CreateCssArea();
  CreateBotBar();
  CreateTimerBar();
  CreateUpgradeBar();
  CreateSectionHideButtons();
  CreateFavicon();
  Object.keys(TooltipText).forEach((i) => {
    CreateSimpleTooltip(TooltipText[i][0], TooltipText[i][1], TooltipText[i][2]);
  });
  CreateWrinklerButtons();
  UpdateBuildingUpgradeStyle();
  createBuildingLockButtons();

  ReplaceTooltips();
  AddWrinklerAreaDetect();

  // Replace native functions
  ReplaceNative();
  ReplaceNativeGrimoire();
  Game.CalculateGains();

  CMLastAscendState = Game.OnAscend;

  if (Game.prefs.popups)
    Game.Popup(`Cookie Monster version ${VersionMajor}.${VersionMinor} loaded!`);
  else Game.Notify(`Cookie Monster version ${VersionMajor}.${VersionMinor} loaded!`, '', '', 1, 1);

  Game.Win('Third-party');
}

;// ./src/Cache/CPS/CurrWrinklerCPS.js




/**
 * This functions caches the current Wrinkler CPS multiplier
 * @global	{number}	CM.Cache.CurrWrinklerCount		Current number of wrinklers
 * @global	{number}	CM.Cache.CurrWrinklerCPSMult	Current multiplier of CPS because of wrinklers (excluding their negative sucking effect)
 */
function CacheCurrWrinklerCPS() {
  CacheCurrWrinklerCPSMult = 0;
  let count = 0;
  Object.keys(Game.wrinklers).forEach((i) => {
    if (Game.wrinklers[i].phase === 2) count += 1;
  });
  let godMult = 1;
  if (SimObjects.Temple.minigameLoaded) {
    const godLvl = Game.hasGod('scorn');
    if (godLvl === 1) godMult *= 1.15;
    else if (godLvl === 2) godMult *= 1.1;
    else if (godLvl === 3) godMult *= 1.05;
  }
  CacheCurrWrinklerCount = count;
  CacheCurrWrinklerCPSMult =
    count *
    (count * 0.05 * 1.1) *
    (Game.Has('Sacrilegious corruption') * 0.05 + 1) *
    (Game.Has('Wrinklerspawn') * 0.05 + 1) *
    godMult;

  FillCMDCache({ CacheCurrWrinklerCount: CacheCurrWrinklerCount, CacheCurrWrinklerCPSMult: CacheCurrWrinklerCPSMult });
}

;// ./src/Cache/CacheLoop.js








 // eslint-disable-line no-unused-vars


/**
 * This functions caches variables that are needed every loop
 * @global	{string}	CM.Cache.TimeTillNextPrestige	Time requried till next prestige level
 */
function LoopCache() {
  // Update Wrinkler Bank
  CacheWrinklers();

  PP_CachePP();
  AllAmountTillNextAchievement(false);
  CacheCurrWrinklerCPS();
  CacheAvgCPS();
  CacheHeavenlyChipsPS();
  CacheAscension();

  const cookiesToNext =
    Game.HowManyCookiesReset(
      Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned)) + 1,
    ) -
    (Game.cookiesEarned + Game.cookiesReset);
  CacheTimeTillNextPrestige = FormatTime(cookiesToNext / GetCPS());
}

;// ./src/Sim/SimulationEvents/SellBuildingForChoEgg.js




/**
 * This function calculates the maximum cookies obtained from selling buildings just before purchasing the chocolate egg
 * It is called by CM.Cache.CacheSellForChoEgg()
 * @returns	{number}	sellTotal	The maximum cookies to be earned
 */
function SellBuildingsForChoEgg() {
  let sellTotal = 0;

  CopyData();

  // Change auras to Earth Shatterer + Reality bending to optimize money made by selling
  let buildingsToSacrifice = 2;
  if (SimDragonAura === 5 || SimDragonAura === 18) {
    buildingsToSacrifice -= 1;
  }
  if (SimDragonAura2 === 5 || SimDragonAura2 === 18) {
    buildingsToSacrifice -= 1;
  }
  SimDragonAura = 5;
  SimDragonAura2 = 18;

  // Sacrifice highest buildings for the aura switch
  for (let i = 0; i < buildingsToSacrifice; ++i) {
    let highestBuilding = 'Cursor';
    Object.keys(SimObjects).forEach((j) => {
      if (SimObjects[j].amount > 0) {
        highestBuilding = j;
      }
    });
    SimObjects[highestBuilding].amount -= 1;
    SimBuildingsOwned -= 1;
  }

  // Get money made by selling all remaining buildings
  Object.keys(SimObjects).forEach((i) => {
    const me = SimObjects[i];
    sellTotal += BuildingSell(
      Game.Objects[me.name],
      Game.Objects[i].basePrice,
      me.amount,
      Game.Objects[i].free,
      me.amount,
    );
  });

  return sellTotal;
}

;// ./src/Cache/CPS/SellChoEgg.js




/**
 * This functions caches the reward for selling the Chocolate egg
 * It is called by CM.Main.Loop()
 * @global	{number}	CM.Cache.SellForChoEgg	Total cookies to be gained from selling Chocolate egg
 */
function CacheSellAllForChoEgg() {
  let sellTotal = 0;
  // Compute cookies earned by selling stock market goods
  if (Game.Objects.Bank.minigameLoaded) {
    const marketGoods = Game.Objects.Bank.minigame.goods;
    let goodsVal = 0;
    Object.keys(marketGoods).forEach((i) => {
      const marketGood = marketGoods[i];
      goodsVal += marketGood.stock * marketGood.val;
    });
    sellTotal += goodsVal * Game.cookiesPsRawHighest;
  }
  // Compute cookies earned by selling all buildings with optimal auras (ES + RB)
  sellTotal += SellBuildingsForChoEgg();
  CacheSellForChoEgg = sellTotal;

  FillCMDCache({ CacheSellForChoEgg: CacheSellForChoEgg });
}

;// ./src/Sim/SimulationEvents/GodChange.js





/**
 * This functions calculates the cps and cost of changing a Dragon Aura
 * It is called by CM.Disp.AddAuraInfo()
 * @param	{number}	god		The number of the slot to be swapped in
 * @param	{number     slot	The slot the god will go to
 * @returns {number} 	CM.Sim.cookiesPs - Game.cookiesPs   The bonus cps and the price of the change
 */
function CalculateChangeGod(god, slot) {
  if (!Game.Objects.Temple.minigameLoaded) return 0;
  CopyData();
  const { minigame } = Game.Objects.Temple;
  const CurrentSlot = minigame.godsById[god].slot;
  if (CurrentSlot === '0') SimGod1 = minigame.slot[slot];
  else if (CurrentSlot === '1') SimGod2 = minigame.slot[slot];
  else if (CurrentSlot === '2') SimGod3 = minigame.slot[slot];

  if (slot === 0) SimGod1 = god;
  else if (slot === 1) SimGod2 = god;
  else if (slot === 2) SimGod3 = god;

  const lastAchievementsOwned = SimAchievementsOwned;
  CalculateGains();

  CheckOtherAchiev();
  if (lastAchievementsOwned !== SimAchievementsOwned) {
    CalculateGains();
  }
  return SimCookiesPs - Game.cookiesPs;
}

;// ./src/Cache/PantheonGods/CacheGods.js




/**
 * This functions caches the cps effect of each God in slot 1, 2 or 3
 */
function CachePantheonGods() {
  for (let god = 0; god < 11; god += 1) {
    for (let slot = 0; slot < 3; slot += 1) {
      CacheGods[god][slot] = CalculateChangeGod(god, slot);
    }
  }

  FillCMDCache({ CacheGods: CacheGods });
}

;// ./src/Disp/HelperFunctions/UpdateAscendState.js





/**
 * This function disables and shows the bars created by CookieMonster when the game is "ascending"
 * It is called by CM.Disp.Draw()
 */
function UpdateAscendState() {
  if (Game.OnAscend) {
    l('game').style.bottom = '0px';
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar === 1)
      l('CMBotBar').style.display = 'none';
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1)
      l('CMTimerBar').style.display = 'none';
  } else {
    ToggleBotBar();
    ToggleTimerBar();
  }
  UpdateBackground();
}

;// ./src/Main/Autoplay/AutoAchievements.js
/**
 * Section: achievements that only take an action
 *
 * Every achievement (shadow ones aside) adds 4% milk, which the kitten upgrades turn into CpS: about +2%
 * CpS each with a dozen kittens and 800% milk. These take nothing but a click in the right place, done
 * the way a player would do them (through the game's own click handlers and menus).
 */

/** Seconds between pokes of the same wrinkler: it regains 1.2 hp per second and loses 0.75 per poke */
const POKE_SECONDS = 1.5;
/** Milliseconds between moving the mouse onto the wrinkler and clicking (it must register as hovered) */
const POKE_DELAY = 250;

/** Seconds between tries at the madeleine, in case the update log cannot show it */
const MADELEINE_RETRY_SECONDS = 600;
/** Window width to shrink to for "Stifling the press" (the game squishes the ticker below 900) */
const NARROW_WIDTH = 880;
/** Milliseconds to wait for the narrow window before giving up, and seconds before trying again */
const SQUISH_WAIT = 3000;
const SQUISH_RETRY_SECONDS = 3600;
/** A gift code stays valid for two days; use it well within that */
const GIFT_CODE_SECONDS = 36 * 3600;

let LastPoke = 0;
let LastMadeleine = 0;
let Squish = null;
let LastSquish = 0;
let Gift = null;

/** The wrinkler being poked for "Wrinkler poker" (bursting sprees spare it) */
const PokeState = { target: null };

/**
 * Clicks the news ticker: 50 clicks for "Tabloid addiction", once in a narrow window for "Stifling the
 * press", and whenever it shows a fortune (fortune upgrades add CpS, the others pay out at once)
 * @returns	{boolean}	Whether it clicked
 */
function ClickTicker() {
  if (!Game.tickerL) return false;
  // In a window narrower than the game's limit, a click squishes the ticker: "Stifling the press"
  const narrow = Game.windowW < Game.tickerTooNarrow && !Game.HasAchiev('Stifling the press');
  const fortune = Game.TickerEffect && Game.TickerEffect.type === 'fortune';
  if (Game.HasAchiev('Tabloid addiction') && !narrow && !fortune) return false;
  Game.tickerL.click();
  return true;
}

/**
 * "Stifling the press" needs the ticker clicked in a window under 900 pixels wide. In the Steam app the
 * page can resize its own window: shrink it for a moment (the ticker click above then counts), and put
 * the size back once the achievement is in or the window did not shrink
 * @returns	{boolean}	Whether it is busy with this
 */
function SquishTicker() {
  if (Squish) {
    if (Game.HasAchiev('Stifling the press') || Date.now() - Squish.since > SQUISH_WAIT) {
      window.resizeTo(Squish.width, Squish.height);
      Squish = null;
      LastSquish = Date.now();
    }
    return true;
  }
  if (
    Game.HasAchiev('Stifling the press') ||
    !window.api || // only the Steam app's page owns its window
    window.outerWidth <= NARROW_WIDTH ||
    Date.now() - LastSquish < SQUISH_RETRY_SECONDS * 1000
  )
    return false;
  Squish = { width: window.outerWidth, height: window.outerHeight, since: Date.now() };
  window.resizeTo(NARROW_WIDTH, window.outerHeight);
  return true;
}

/**
 * "Baby it's old outside": during Christmas some grandmas in the grandma row are Santa's helpers, and
 * pressing the mouse on one counts. Points the row's mouse at a helper with the button down for one
 * redraw of the row, as hovering and pressing would
 * @returns	{boolean}	Whether it tried
 */
function ElfGrandma() {
  const me = Game.Objects.Grandma;
  if (Game.HasAchiev("Baby it's old outside") || Game.season !== 'christmas' || !me.amount)
    return false;
  const elf = me.pics.find((pic) => pic.pic === 'elfGrandma.png');
  if (!elf) {
    me.redraw(); // the pictures predate Christmas: draw them again from the season's list
    return true;
  }
  const { mouseDown } = Game;
  me.mouseOn = true;
  me.mousePos = [elf.x + 32, elf.y + 32];
  Game.mouseDown = 1;
  try {
    me.draw();
  } finally {
    me.mouseOn = false;
    me.mousePos = [-100, -100];
    Game.mouseDown = mouseDown;
  }
  return true;
}

/**
 * "No time like the present": with Wrapping paper, sends a gift of 1 cookie to keep its code, then
 * redeems the code once the hour of "Gifted out" that sending starts is over
 * @returns	{boolean}	Whether it did something
 */
function SelfGift() {
  if (
    Game.HasAchiev('No time like the present') ||
    !Game.Has('Wrapping paper') ||
    Game.ascensionMode !== 0 ||
    Game.cookies < 1e9 ||
    Game.hasBuff('Gifted out') ||
    Game.promptOn
  )
    return false;
  if (!Gift || Date.now() - Gift.time > GIFT_CODE_SECONDS * 1000) {
    Game.promptGiftSend();
    if (l('giftAmount') && l('promptOption0')) {
      l('giftAmount').value = 1;
      l('promptOption0').click();
      if (l('giftCode') && l('giftCode').value) Gift = { code: l('giftCode').value, time: Date.now() };
    }
    Game.ClosePrompt();
    return true;
  }
  Game.promptGiftRedeem();
  if (l('giftCode') && l('promptOption0')) {
    l('giftCode').value = Gift.code;
    l('giftCode').dispatchEvent(new Event('change'));
    l('promptOption0').click();
  }
  Game.ClosePrompt();
  Gift = null;
  return true;
}

/**
 * Finds the forgotten madeleine at the bottom of the update log, then goes back to the menu that was open
 * @returns	{boolean}	Whether it found it
 */
function FindMadeleine() {
  if (Game.HasAchiev('Olden days') || Date.now() - LastMadeleine < MADELEINE_RETRY_SECONDS * 1000)
    return false;
  LastMadeleine = Date.now();
  const previous = Game.onMenu;
  if (previous !== 'log') Game.ShowMenu('log');
  const madeleine = l('oldenDays');
  if (madeleine && madeleine.firstChild) madeleine.firstChild.click();
  if (previous !== 'log') Game.ShowMenu(previous);
  return true;
}

/**
 * "Wrinkler poker": pokes one wrinkler 50 times without bursting it. Moves the mouse onto the wrinkler,
 * then clicks once the game has registered it as hovered
 * @returns	{boolean}	Whether it is busy poking
 */
function PokeWrinkler() {
  if (Game.HasAchiev('Wrinkler poker') || !Game.wrinklers) return false;
  if (!PokeState.target || PokeState.target.phase !== 2 || PokeState.target.type !== 0) {
    PokeState.target = Game.wrinklers.find((me) => me.phase === 2 && me.type === 0) || null;
    if (!PokeState.target) return false;
  }
  const { target } = PokeState;
  if (target.hp < Game.wrinklerHP - 0.05 || Date.now() - LastPoke < POKE_SECONDS * 1000) return true;
  LastPoke = Date.now();
  Game.mouseX = target.x;
  Game.mouseY = target.y;
  setTimeout(() => {
    Game.mouseX = target.x;
    Game.mouseY = target.y;
    if (target.selected && l('backgroundLeftCanvas'))
      l('backgroundLeftCanvas').dispatchEvent(new MouseEvent('click', { bubbles: true }));
  }, POKE_DELAY);
  return true;
}

/**
 * Takes the next action-only achievement, one per call
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoAchievements() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (
    !settings.AutoAchievements ||
    Game.OnAscend ||
    Game.AscendTimer > 0 ||
    Game.ReincarnateTimer > 0
  )
    return;
  if (!Game.HasAchiev('Here you go')) {
    Game.Achievements['Here you go'].click();
    return;
  }
  if (!Game.HasAchiev('Tiny cookie')) {
    Game.ClickTinyCookie();
    return;
  }
  if (!Game.HasAchiev('Just wrong') && Game.Objects.Grandma.amount > 1) {
    Game.Objects.Grandma.sell(1);
    return;
  }
  if (FindMadeleine()) return;
  if (SquishTicker() && Game.windowW >= Game.tickerTooNarrow) return;
  if (ClickTicker()) return;
  if (ElfGrandma()) return;
  if (SelfGift()) return;
  PokeWrinkler();
}

;// ./src/Main/CheckStates/Ascension.js





/** Seconds the plan has to keep saying "ascend now" before acting on it */
const SUSTAIN_SECONDS = 10;

/** Start date of the run that has been alerted, and since when the current run has been ready */
let AlertedRun = null;
let ReadySince = null;

/**
 * Seconds for which the plan has continuously said to ascend now (0 when it does not)
 * @returns	{number}
 */
function ReadySeconds() {
  return ReadySince === null ? 0 : (Date.now() - ReadySince) / 1000;
}

/**
 * This function tracks whether ascending is optimal and alerts once per run when it becomes so
 * It is called by CM.Main.Loop
 */
function CheckAscensionReady() {
  const { applicable, plan } = AscensionCache;
  if (
    !applicable ||
    plan === null ||
    !plan.applicable ||
    Game.OnAscend ||
    Game.AscendTimer > 0 ||
    window.cookieMonsterFrameworkData.isInitializing
  ) {
    ReadySince = null;
    return;
  }
  if (!plan.ascendNow || plan.levelsNow < 1) {
    ReadySince = null;
    return;
  }
  if (ReadySince === null) ReadySince = Date.now();
  if (ReadySeconds() < SUSTAIN_SECONDS || AlertedRun === Game.startDate) return;

  AlertedRun = Game.startDate;
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (settings.AutoAscend) return; // Autoplay ascends by itself
  const message = `Ascending now grants ${Beautify_Beautify(plan.levelsNow)} prestige level${
    plan.levelsNow === 1 ? '' : 's'
  } (+${FormatPercent(plan.speedGainNow * 100)} production in every future run).`;
  notificationsFunctions.createFlash('cookieMonsterMod', 3, 'AscendFlash', false);
  notificationsFunctions.playCMSound('cookieMonsterMod', settings.AscendSoundURL, 'AscendSound', 'AscendVolume', false);
  notificationsFunctions.createNotification('cookieMonsterMod', 'AscendNotification', 'Time to ascend', message);
  if (settings.AscendNote)
    Game.Notify(
      'Optimal time to ascend',
      `${message}<br>Pop wrinklers and buy the Chocolate egg (if unlocked) first.`,
      [19, 7],
    );
}

;// ./src/Main/Autoplay/AutoMarket.js
/**
 * Section: the Stock Market under autoplay
 *
 * Goods cost "dollars", seconds of the highest raw CpS of the run, and their prices drift back toward a
 * resting value of 10 + 10 * (good index) + (bank level - 1). Buying carries an overhead of 20% (less with
 * brokers); selling is free. Buying well below the resting value and selling at or above it therefore
 * clears the overhead with room to spare, using only the prices the market shows. Spending is capped to
 * a share of the bank so the market never starves the auto-buyer.
 *
 * The offices are upgraded whenever the cursors allow (it sacrifices cheap cursors and needs cursor
 * levels), since they open loans. A loan multiplies CpS for a while against a down payment of part of the
 * bank, and then divides it for longer; ascending before the interest starts avoids it ("Debt evasion").
 * So a loan is taken once the ascension planner expects the run to end before it runs out, even on its
 * slow estimate, and the ascension routine ends the run early rather than pay the interest.
 */



/** Buy below this share of a good's resting value, sell at or above SELL_AT */
const BUY_BELOW = 0.6;
const SELL_AT = 1;
/** Share of the bank (above any reserve) the market may hold in goods at once */
const BANK_SHARE = 0.1;

/**
 * Loans: CpS multiplier, its seconds, the interest multiplier and its seconds, and the office level
 * above which the loan is offered (from the game's loan table and bank display)
 */
const LOANS = [
  { id: 1, mult: 1.5, seconds: 2 * 3600, interest: 0.25, interestSeconds: 4 * 3600, office: 1 },
  { id: 2, mult: 2, seconds: 40, interest: 0.1, interestSeconds: 40 * 60, office: 3 },
  { id: 3, mult: 1.2, seconds: 48 * 3600, interest: 0.8, interestSeconds: 120 * 3600, office: 4 },
];
/** Share of the loan's time the planner's slow estimate of the run may use up */
const LOAN_MARGIN = 0.9;

/**
 * Loans the offices offer now and that are not running (nor their interest)
 * @returns	{object[]}	Entries of LOANS
 */
function AvailableLoans() {
  const bank = Game.Objects.Bank;
  if (!bank.minigameLoaded || !bank.minigame || Game.ascensionMode !== 0) return [];
  const M = bank.minigame;
  return LOANS.filter(
    (loan) =>
      M.officeLevel > loan.office &&
      !Game.hasBuff(`Loan ${loan.id}`) &&
      !Game.hasBuff(`Loan ${loan.id} (interest)`),
  );
}

/**
 * Takes the loans whose boost outlasts the rest of the run on the planner's slow estimate
 */
function TakeLoans() {
  const { plan } = AscensionCache;
  if (!plan || !plan.applicable || !Number.isFinite(plan.remainingSlow)) return;
  AvailableLoans().forEach((loan) => {
    if (loan.id !== 2 && plan.remainingSlow <= LOAN_MARGIN * loan.seconds)
      Game.Objects.Bank.minigame.takeLoan(loan.id);
  });
}

/**
 * Upgrades the office when the cursors allow, as its button does
 * @returns	{boolean}	Whether it upgraded
 */
function UpgradeOffice() {
  const M = Game.Objects.Bank.minigame;
  const office = M.offices[M.officeLevel];
  const cursor = Game.Objects.Cursor;
  if (!office || !office.cost || !l('bankOfficeUpgrade')) return false;
  if (cursor.amount < office.cost[0] || cursor.level < office.cost[1]) return false;
  l('bankOfficeUpgrade').click();
  return true;
}

/**
 * Cookies currently tied up in goods, at today's prices
 * @param	{object}	M	Market minigame
 * @returns	{number}
 */
function Holdings(M) {
  return M.goodsById.reduce(
    (sum, me) => sum + me.stock * M.getGoodPrice(me) * Game.cookiesPsRawHighest,
    0,
  );
}

/**
 * Upgrades the office, takes loans that will not reach their interest, and trades every active good:
 * sells what reached its resting value, buys what fell far below it
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoMarket() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const bank = Game.Objects.Bank;
  if (!settings.AutoMarket || !bank.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0) return;
  const M = bank.minigame;
  if (!M || !M.goodsById) return;
  if (UpgradeOffice()) return;
  TakeLoans();
  for (let id = 0; id < M.goodsById.length; id++) {
    const me = M.goodsById[id];
    if (me.active) {
      const rest = M.getRestingVal(id);
      const price = M.getGoodPrice(me);
      if (me.stock > 0 && price >= rest * SELL_AT && M.sellGood(id, me.stock)) return;
      if (price <= rest * BUY_BELOW && me.stock < M.getGoodMaxStock(me)) {
        const overhead = 1 + 0.01 * (20 * 0.95 ** M.brokers);
        const unit = Game.cookiesPsRawHighest * price * overhead;
        const budget = Game.cookies * BANK_SHARE - Holdings(M);
        const n = Math.min(M.getGoodMaxStock(me) - me.stock, Math.floor(budget / unit));
        if (n > 0 && M.buyGood(id, n)) return;
      }
    }
  }
}

;// ./src/Main/Autoplay/AutoAscend.js











/** Seconds to let wrinklers pop before ascending, and to show the heavenly screen before leaving it */
const CASH_IN_SECONDS = 2;
const HEAVEN_SECONDS = 1.5;
/** Seconds before a loan runs out at which the run may end early to avoid its interest */
const LOAN_EXIT_SECONDS = 60;

let Phase = 'idle';
let PhaseSince = 0;
/** Whether the run being left is a Born again run */
let LeavingChallenge = false;

/**
 * Buys a heavenly upgrade after the unowned parents it requires, as the ascension screen only allows
 * upgrades whose parents are all owned
 * @param	{object}	me	A heavenly upgrade
 * @returns	{boolean}	Whether it is owned afterwards
 */
function BuyWithParents(me) {
  if (me.bought) return true;
  if (me.showIf && !me.showIf()) return false;
  for (let i = 0; i < me.parents.length; i++) {
    if (me.parents[i] !== -1 && !BuyWithParents(me.parents[i])) return false;
  }
  return me.getPrice() <= Game.heavenlyChips && me.buy() === 1;
}

/** Permanent upgrade slots, in the order of Game.permanentUpgrades */
const PERMANENT_SLOTS = [
  'Permanent upgrade slot I',
  'Permanent upgrade slot II',
  'Permanent upgrade slot III',
  'Permanent upgrade slot IV',
  'Permanent upgrade slot V',
];

/**
 * How much an upgrade kept in a permanent slot multiplies CpS at the start of a run, as a logarithm:
 * milk carries over, so a kitten multiplies CpS by 1 + k * milk at once, and a cookie by 1 + its power;
 * other upgrades act on buildings the run has yet to buy
 * @param	{object}	me	Upgrade
 * @returns	{number}
 */
function StartValue(me) {
  const k = KittenMilkFactor(me.name);
  if (k) return Math.log1p(k * (Game.milkProgress || 0) * MilkMultiplier());
  const power = typeof me.power === 'function' ? me.power(me) : me.power;
  return me.pool === 'cookie' && power > 0 ? Math.log1p(power / 100) : 0;
}

/**
 * Puts the upgrades worth most at the start of a run into the permanent slots owned, as picking them in
 * the ascension screen does (candidates are the upgrades bought last run that the game allows there)
 */
function FillPermanentSlots() {
  const owned = PERMANENT_SLOTS.map((name, i) => (Game.Has(name) ? i : -1)).filter((i) => i !== -1);
  if (!owned.length) return;
  const candidates = Object.keys(Game.Upgrades)
    .map((name) => Game.Upgrades[name])
    .filter(
      (me) =>
        me.bought &&
        me.unlocked &&
        !me.noPerm &&
        (me.pool === '' || me.pool === 'cookie') &&
        StartValue(me) > 0,
    )
    .sort((a, b) => StartValue(b) - StartValue(a));
  owned.forEach((slot, i) => {
    if (candidates[i]) Game.permanentUpgrades[slot] = candidates[i].id;
  });
  if (Game.BuildAscendTree) Game.BuildAscendTree();
}

/**
 * Spends heavenly chips: Legacy first, then along the purchase order the ascension planner assumes
 * (best production gain per chip, parents included), buying as many items as the chips cover and
 * saving the rest for the next one; then fills the permanent upgrade slots
 */
function SpendHeavenlyChips() {
  if (!BuyWithParents(Game.Upgrades.Legacy)) return;
  const context =
    AscensionCache.heavenlyContext || HeavenlyContext(Game.cookiesPs, AutoClickIncome());
  const order = HeavenlyPurchaseOrder(context);
  for (let i = 0; i < order.length && order[i].cost <= Game.heavenlyChips; i++) {
    order[i].bundle.forEach((me) => {
      if (!me.bought) me.buy();
    });
  }
  FillPermanentSlots();
}

/**
 * Whether ending the run now costs less than the interest of a loan about to run out: the interest
 * divides CpS for hours, which delays the run by about (1 - multiplier) of the time it covers
 * @returns	{boolean}
 */
function LoanExit() {
  const { plan } = AscensionCache;
  if (!plan || !plan.applicable || plan.costOfAscendingNow === null) return false;
  return LOANS.some((loan) => {
    const buff = Game.hasBuff(`Loan ${loan.id}`);
    if (!buff || buff.time / Game.fps > LOAN_EXIT_SECONDS) return false;
    const penalty = (1 - loan.interest) * Math.min(loan.interestSeconds, plan.remaining);
    return plan.costOfAscendingNow < penalty;
  });
}

/**
 * Ascends when the advisor has said so for SUSTAIN_SECONDS (or a Born again run is over): pops normal
 * wrinklers and buys the Chocolate egg first, spends the heavenly chips and reincarnates, into a Born
 * again run when the challenge achievements are due
 * It is called every logic frame, also while ascending
 */
function AutoAscend() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const now = Date.now();
  const elapsed = (now - PhaseSince) / 1000;
  const enter = (phase) => {
    Phase = phase;
    PhaseSince = now;
  };

  if (Phase === 'idle') {
    if (!settings.AutoAscend || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
      return;
    if (ChallengeRun() ? !ChallengeDone() : ReadySeconds() < SUSTAIN_SECONDS && !LoanExit())
      return;
    if (CacheWrinklersNormal > 0) PopAllNormalWrinklers();
    const egg = Game.Upgrades['Chocolate egg'];
    if (egg && egg.unlocked && !egg.bought) egg.buy();
    enter('cashing');
  } else if (Phase === 'cashing') {
    if (elapsed < CASH_IN_SECONDS) return;
    const { plan } = AscensionCache;
    LeavingChallenge = ChallengeRun();
    if (
      !settings.AutoAscend ||
      (!LeavingChallenge && (!plan || !plan.ascendNow) && !LoanExit())
    ) {
      enter('idle');
      return;
    }
    // The bank is about to be lost, so a loan's down payment costs nothing now: "Debt evasion"
    const loans = AvailableLoans();
    if (!Game.HasAchiev('Debt evasion') && loans.length)
      Game.Objects.Bank.minigame.takeLoan(loans[0].id);
    if (LeavingChallenge)
      Game.Notify(
        'Cookie Monster+ ended the Born again run',
        `Neverclick: ${Game.HasAchiev('Neverclick') ? 'won' : 'missed'}, Hardcore: ${
          Game.HasAchiev('Hardcore') ? 'won' : 'missed'
        }. Back to a normal run.`,
        [10, 0],
      );
    else
      Game.Notify(
        'Cookie Monster+ ascended',
        `+${Beautify_Beautify(plan.levelsNow)} prestige levels, +${FormatPercent(
          plan.speedGainNow * 100,
        )} production in every future run.`,
        [19, 7],
      );
    Game.Ascend(1);
    enter('ascending');
  } else if (Phase === 'ascending') {
    if (Game.OnAscend) enter('heaven');
    else if (elapsed > 30 && Game.AscendTimer === 0) enter('idle');
  } else if (Phase === 'heaven') {
    if (!Game.OnAscend) enter('idle');
    else if (elapsed >= HEAVEN_SECONDS) {
      SpendHeavenlyChips();
      Game.nextAscensionMode = ChallengeDue(LeavingChallenge) ? 1 : 0;
      Game.Reincarnate(1);
      enter('reincarnating');
    }
  } else if (Phase === 'reincarnating' && !Game.OnAscend && Game.ReincarnateTimer === 0) {
    enter('idle');
  }
}

;// ./src/Main/Autoplay/AutoClick.js


/** The game ignores clicks less than 20 ms apart, so more than 50 per second is pointless */
const MAX_RATE = 50;

let ClickTimer = null;
let ClickInterval = 0;

/**
 * Clicks the big cookie once, without the click sound and with particles drawn on the cookie rather
 * than under the player's mouse
 */
function ClickOnce() {
  if (!Game.ready || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0) return;
  if (!ClicksAllowed()) return;
  const playSound = Game.playCookieClickSound;
  const { mouseX, mouseY } = Game;
  Game.playCookieClickSound = function () {};
  Game.mouseX = Game.cookieOriginX;
  Game.mouseY = Game.cookieOriginY;
  try {
    Game.ClickCookie();
  } finally {
    Game.playCookieClickSound = playSound;
    Game.mouseX = mouseX;
    Game.mouseY = mouseY;
  }
}

/**
 * Starts, stops or retimes the clicker to match the settings
 * Clicks run on their own timer because the game limits clicks by real time, not by game frames
 */
function UpdateAutoClicker() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const rate = settings.AutoClick
    ? Math.min(Math.max(Number(settings.AutoClickRate) || 0, 0), MAX_RATE)
    : 0;
  const interval = rate > 0 ? Math.round(1000 / rate) : 0;
  if (interval === ClickInterval) return;
  if (ClickTimer !== null) clearInterval(ClickTimer);
  ClickTimer = interval > 0 ? setInterval(ClickOnce, interval) : null;
  ClickInterval = interval;
}

;// ./src/Main/Autoplay/AutoLumps.js
/**
 * Section: sugar lumps under autoplay
 *
 * Ripe lumps are harvested at once. Lumps go first to the minigames, which are worth far more than a
 * building level (the Pantheon holds Godzamok), then to the Sugar frenzy each run once Sugar craving is
 * owned (triple CpS for an hour: two hours of income for one lump), then to cursor levels up to 4, which
 * the Stock Market's offices require before they open the first loan (+50% CpS for the last two hours of
 * every run), and then to building levels, which are permanent: each level adds 1% to that building's
 * CpS, and level 10 also earns an achievement (more milk).
 */



/** Minigame buildings, most valuable first under autoplay */
const MINIGAME_ORDER = ['Temple', 'Wizard tower', 'Farm', 'Bank'];
/** Cursor level the second office upgrade requires, which opens the first loan */
const LOAN_CURSOR_LEVEL = 4;

/** Set by the Pantheon when a much better arrangement waits for worship swaps that a lump would refill */
const LumpState = { holdForSwaps: false };

/**
 * Accepts the game's confirmation prompt with the given id, as a player clicking "Yes" would
 * @param	{string}	id	Prompt id
 */
function ConfirmPrompt(id) {
  if (Game.promptOn && l(`promptContent${id}`) && l('promptOption0')) l('promptOption0').click();
}

/**
 * Raises a building's level by one with sugar lumps, accepting the game's prompt
 * @param	{object}	me	Building
 */
function LevelUp(me) {
  me.levelUp();
  ConfirmPrompt('SpendLump');
}

/**
 * Share of CpS gained per lump by the next level of a building: a level adds 1% of the building's CpS
 * before levels, costs (level + 1) lumps, and level 10 earns an achievement
 * @param	{object}	me	Building
 * @param	{number}	totalCps	Sum of the buildings' CpS
 * @returns	{number}
 */
function LevelValue(me, totalCps) {
  const cost = me.level + 1;
  const share = totalCps > 0 ? me.storedTotalCps / totalCps : 0;
  let gain = (0.01 * share) / (1 + 0.01 * me.level);
  if (me.level + 1 === 10 && me.levelAchiev10 && !Game.HasAchiev(me.levelAchiev10.name))
    gain += AchievementValue();
  return gain / cost;
}

/**
 * Activates the Sugar frenzy (once per ascension, with Sugar craving), accepting the game's prompt
 * @returns	{boolean}	Whether it did
 */
function SugarFrenzy() {
  const me = Game.Upgrades['Sugar frenzy'];
  if (!me || !me.unlocked || me.bought || Game.lumps < 1 || !me.clickFunction) return false;
  me.clickFunction();
  ConfirmPrompt('SpendLump');
  return true;
}

/**
 * Spends lumps: minigames first, then the Sugar frenzy, then cursor levels for the first loan, then the
 * building level with the best gain per lump, saving up for each when it costs more than the lumps at
 * hand (spending on something worse first would only delay it). With "Sugar baking" every unspent lump
 * (up to 100) already adds 1% of CpS, more than any level
 */
function SpendLumps() {
  if (LumpState.holdForSwaps) return;
  for (let i = 0; i < MINIGAME_ORDER.length; i++) {
    const me = Game.Objects[MINIGAME_ORDER[i]];
    if (me && me.level === 0 && me.amount > 0) {
      if (Game.lumps >= 1) LevelUp(me);
      return;
    }
  }
  if (SugarFrenzy()) return;
  const cursor = Game.Objects.Cursor;
  if (Game.Objects.Bank.minigameLoaded && cursor.level < LOAN_CURSOR_LEVEL) {
    if (Game.lumps >= cursor.level + 1) LevelUp(cursor);
    return;
  }
  if (Game.Has('Sugar baking') && Game.lumps <= 100) return;
  const totalCps = Object.keys(Game.Objects).reduce(
    (sum, name) => sum + Game.Objects[name].storedTotalCps,
    0,
  );
  let best = null;
  let bestValue = 0;
  Object.keys(Game.Objects).forEach((name) => {
    const me = Game.Objects[name];
    if (me.amount === 0) return;
    const value = LevelValue(me, totalCps);
    if (value > bestValue) {
      best = me;
      bestValue = value;
    }
  });
  if (best && Game.lumps >= best.level + 1) LevelUp(best);
}

/**
 * Harvests ripe lumps, tries "Hand-picked" once the minigames are open (a mature but unripe lump yields
 * nothing half the time, so it costs half a lump a try), and spends lumps
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoLumps() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoLumps || !Game.canLumps() || Game.OnAscend || Game.AscendTimer > 0) return;
  const age = Date.now() - Game.lumpT;
  if (age >= Game.lumpRipeAge) {
    Game.clickLump();
    return;
  }
  const minigamesDone = MINIGAME_ORDER.every(
    (name) => !Game.Objects[name] || Game.Objects[name].level > 0,
  );
  if (!Game.HasAchiev('Hand-picked') && minigamesDone && age >= Game.lumpMatureAge) {
    Game.clickLump();
    return;
  }
  SpendLumps();
}

;// ./src/Main/Autoplay/AutoDragon.js
/**
 * Section: the dragon under autoplay
 *
 * The dragon starts over every run. Training costs cookies for the first levels and then 100 of each
 * building in turn; the payoffs are Radiant Appetite (all production x2, level 19), Dragon Guts (two more
 * wrinklers that digest and return 20% more, level 25), the dragon cookie and the second aura. Training
 * toward the next payoff goes ahead when buying the sacrificed buildings back costs at most an hour of
 * income (a quarter of an hour for the smaller steps). Auras are picked by trying them in the game's CpS
 * formula and the auto-buyer's income model, and changed only when the gain pays back the building a
 * change costs within half an hour.
 */




/** Dragon levels after which a payoff is available, and seconds of income worth paying for each */
const MILESTONES = [
  { level: 19, budget: 3600 }, // Radiant Appetite
  { level: 25, budget: 3600 }, // Dragon Guts
  { level: 26, budget: 900 }, // dragon cookie
  { level: 27, budget: 1800 }, // second aura, "Here be dragon"
];
/** Auras the model can value; the rest work through selling, drops, sugar lumps or minigames */
const AURA_NAMES = [
  'Breath of Milk',
  'Dragon Cursor',
  'Elder Battalion',
  'Dragon God',
  'Arcane Aura',
  'Epoch Manipulator',
  'Radiant Appetite',
  'Reality Bending',
  'Dragon Guts',
];
/** Seconds within which a new aura must pay back the building that switching costs */
const AURA_PAYBACK = 1800;
/** Seconds between aura re-evaluations (and right after every training step) */
const AURA_CHECK_SECONDS = 60;

let LastAuraCheck = 0;

/**
 * Cookies to buy back n of a building after sacrificing them: the copies below the current amount cost
 * price / 1.15^k for k = 1..n, a sum of price * (1 - 1.15^-n) / 0.15
 * @param	{object}	me	Building
 * @param	{number}	n	Copies sacrificed
 * @returns	{number}
 */
function RebuyCost(me, n) {
  return (me.getPrice() * (1 - 1.15 ** -n)) / 0.15;
}

/**
 * Cookies the training step from a dragon level costs
 * @param	{number}	level	Dragon level
 * @returns	{number}
 */
function StepCost(level) {
  const objects = Object.keys(Game.Objects).map((name) => Game.Objects[name]);
  if (level < 5) return 1000000 * 2 ** level;
  if (level < 25) return RebuyCost(objects[level - 5], 100);
  const n = level === 25 ? 50 : 200;
  return objects.reduce((sum, me) => sum + RebuyCost(me, n), 0);
}

/**
 * Copies of each building the training steps from `from` up to `to` need at hand: steps 5 to 24 take
 * 100 of one building each, then the dragon cookie takes 50 and the second aura 200 of every building
 * (after the earlier sacrifices)
 * @param	{number}	from	Dragon level
 * @param	{number}	to	Dragon level reached
 * @returns	{boolean}	Whether the buildings are there now
 */
function PathAvailable(from, to) {
  const objects = Object.keys(Game.Objects).map((name) => Game.Objects[name]);
  const taken = objects.map(() => 0);
  for (let l = Math.max(from, 5); l < to; l++) {
    if (l < 25) {
      if (objects[l - 5].amount - taken[l - 5] < 100) return false;
      taken[l - 5] += 100;
    } else {
      const need = l === 25 ? 50 : 200;
      if (objects.some((me, i) => me.amount - taken[i] < need)) return false;
    }
  }
  return true;
}

/**
 * Whether training the next level goes ahead. The first five levels only cost a few million cookies
 * (and teach Breath of Milk). After that each step sacrifices buildings and pays off only at the next
 * milestone, so the steps go ahead once every building the way there needs is at hand and buying them
 * all back costs no more than that milestone's budget in seconds of income
 * @returns	{boolean}
 */
function TrainingPays() {
  const level = Game.dragonLevel;
  if (level >= Game.dragonLevels.length - 1 || !Game.dragonLevels[level].cost()) return false;
  if (level < 5) return true;
  const milestone = MILESTONES.find((m) => m.level > level);
  if (!milestone || !PathAvailable(level, milestone.level)) return false;
  let cost = 0;
  for (let l = level; l < milestone.level; l++) cost += StepCost(l);
  return cost <= AutoplayEconomy(Game.cookies).income * milestone.budget;
}

/**
 * Long-run income with the given auras: sets them, lets the game recompute CpS, scores the result and
 * restores the auras. Arcane Aura also brings golden cookies 5% sooner
 * @param	{number}	primary	Aura id
 * @param	{number}	secondary	Aura id
 * @returns	{number}	Cookies per second
 */
function ScoreAuras(primary, secondary) {
  const saved = [Game.dragonAura, Game.dragonAura2];
  const arcane = Number(
    Object.keys(Game.dragonAuras).find((k) => Game.dragonAuras[k].name === 'Arcane Aura'),
  );
  const before = 1 - Game.auraMult('Arcane Aura') * 0.05;
  Game.dragonAura = primary;
  Game.dragonAura2 = secondary;
  Game.CalculateGains();
  const after = 1 - Game.auraMult('Arcane Aura') * 0.05;
  const { income } = AutoplayEconomy(Game.cookies, Number.isFinite(arcane) ? after / before : 1);
  [Game.dragonAura, Game.dragonAura2] = saved;
  Game.CalculateGains();
  return income;
}

/**
 * Sets an aura through the game's own aura prompt, which charges one of the highest buildings
 * @param	{number}	aura	Aura id
 * @param	{number}	slot	0 for the primary aura, 1 for the secondary
 */
function SetAura(aura, slot) {
  Game.SetDragonAura(aura, slot);
  ConfirmPrompt('PickDragonAura');
  if (Game.specialTab) Game.ToggleSpecialMenu(0);
}

/**
 * Picks the best primary aura (and secondary once trained), switching only when it pays
 */
function ChooseAuras() {
  if (Date.now() - LastAuraCheck < AURA_CHECK_SECONDS * 1000) return;
  LastAuraCheck = Date.now();
  const ids = AURA_NAMES.map((name) =>
    Number(Object.keys(Game.dragonAuras).find((k) => Game.dragonAuras[k].name === name)),
  ).filter((id) => Number.isFinite(id) && Game.dragonLevel >= id + 4);
  if (!ids.length) return;
  const twoAuras = Game.dragonLevel >= Game.dragonLevels.length - 1;
  const current = ScoreAuras(Game.dragonAura, Game.dragonAura2);
  let best = [Game.dragonAura, Game.dragonAura2];
  let bestIncome = current;
  ids.forEach((a) => {
    (twoAuras ? ids : [Game.dragonAura2]).forEach((b) => {
      if (a === b && a !== 0) return;
      const income = ScoreAuras(a, b);
      if (income > bestIncome) {
        best = [a, b];
        bestIncome = income;
      }
    });
  });
  let highest = null;
  Object.keys(Game.Objects).forEach((name) => {
    if (Game.Objects[name].amount > 0) highest = Game.Objects[name];
  });
  const switchCost = highest ? highest.getPrice() / 1.15 : 0;
  const changes = Number(best[0] !== Game.dragonAura) + Number(best[1] !== Game.dragonAura2);
  if (!changes || (bestIncome - current) * AURA_PAYBACK < switchCost * changes) return;
  if (best[0] !== Game.dragonAura) SetAura(best[0], 0);
  else if (best[1] !== Game.dragonAura2) SetAura(best[1], 1);
}

/** Upgrades petting the dragon can drop, one per quarter of an hour, and seconds between petting sessions */
const DRAGON_DROPS = ['Dragon scale', 'Dragon claw', 'Dragon fang', 'Dragon teddy bear'];
const PET_SECONDS = 60;
/** Pets per session: each has a 1 in 20 chance to drop the current quarter-hour's upgrade */
const PETS = 20;

let LastPet = 0;

/**
 * With "Pet the dragon", pets the dragon in its menu until this quarter-hour's drop shows up (each drop
 * is an upgrade for this run)
 * @returns	{boolean}	Whether it petted
 */
function PetDragon() {
  if (!Game.Has('Pet the dragon') || Game.dragonLevel < 8) return false;
  if (DRAGON_DROPS.every((name) => Game.Has(name) || Game.HasUnlocked(name))) return false;
  if (Date.now() - LastPet < PET_SECONDS * 1000) return false;
  LastPet = Date.now();
  const { volume } = Game;
  Game.volume = 0;
  Game.specialTab = 'dragon';
  Game.ToggleSpecialMenu(1);
  for (let i = 0; i < PETS; i++) Game.ClickSpecialPic();
  Game.ToggleSpecialMenu(0);
  Game.volume = volume;
  return true;
}

/**
 * Buys the dragon egg, trains the dragon, pets it for its drops and picks its auras
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoDragon() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoDragon || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  const egg = Game.Upgrades['A crumbly egg'];
  if (!egg) return;
  if (!egg.bought) {
    if (egg.unlocked && Game.cookies >= egg.getPrice()) egg.buy();
    return;
  }
  if (TrainingPays()) {
    Game.UpgradeDragon();
    if (Game.specialTab) Game.ToggleSpecialMenu(0);
    LastAuraCheck = 0;
    return;
  }
  if (PetDragon()) return;
  ChooseAuras();
}

;// ./src/Main/Autoplay/AutoElder.js
/**
 * Section: the Grandmapocalypse under autoplay
 *
 * Research goes all the way to the Elder Pact: the upgrades on the way add CpS, and the pact makes the
 * Elder Pledge come back by itself at a price that stops growing at 8^14 cookies, nothing late in a run.
 * A pledge holds the wrath off for half an hour (an hour with Sacrificial rolling pins), so autoplay picks
 * the stage that earns more: wrath (wrath cookies, and wrinklers that turn CpS into about six times as
 * much income) or calm (golden cookies, whose Frenzies also multiply click income). It compares the
 * long-run income of both and pledges whenever calm wins, which it does once Godzamok makes clicks most
 * of the income. Otherwise it keeps its wrinklers and pops them when cashing in beats keeping them. It
 * takes the elder achievements on the way (pledge, covenant and revoke five times), and bursts every
 * wrinkler that appears for "Wrinklesquisher" and "Moistburster" (50 and 200 in one run) when what they
 * are worth beats the income given up meanwhile.
 */





/** Research that starts and deepens the Grandmapocalypse; the game asks for confirmation first */
const ELDER_RESEARCH = ['One mind', 'Communal brainsweep', 'Elder Pact'];
/** Seconds a new wrinkler spends crawling to the cookie before it starts digesting */
const CRAWL_SECONDS = 10;
/** Run length assumed when the ascension planner has no estimate */
const DEFAULT_REMAINING = 7200;
/** Wrinklers burst in one run for each achievement */
const SPREE_TARGETS = [
  ['Wrinklesquisher', 50],
  ['Moistburster', 200],
];
/** Seconds between comparisons of the stages */
const STAGE_CHECK_SECONDS = 10;

let LastStageCheck = 0;
let Stages = null;

/**
 * Average seconds a free wrinkler slot stays empty, from the game's spawn chance per frame
 * @param	{number}	[wrath]	Elder wrath to assume (the current one by default)
 * @returns	{number}
 */
function WrinklerRespawnSeconds(wrath = Game.elderWrath) {
  let chance = 0.00001 * wrath * Game.eff('wrinklerSpawn');
  if (Game.Has('Unholy bait')) chance *= 5;
  if (Game.hasGod) chance *= [1, 2.5, 2, 1.5][Game.hasGod('scorn') || 0];
  if (Game.Has('Wrinkler doormat')) chance = 0.1;
  return chance > 0 ? 1 / (chance * Game.fps) + CRAWL_SECONDS : Infinity;
}

/**
 * Cookies a wrinkler must hold before popping it pays. Popped now, its cookies grow with the economy
 * for the rest of the run, a factor e^(rho T) - 1 more by the end (income grows like t^(beta - 1) in a
 * run whose cookies grow like t^beta, so rho = (beta - 1) / t). Its slot meanwhile stays empty for the
 * respawn time, and the other n - 1 wrinklers each digest a twentieth less: about (2n - 1) / 20 of CpS
 * goes missing, returned x1.1, minus the twentieth of CpS that is no longer withered. Pop when the gain
 * beats that loss, which also compounds until the end
 * @param	{number}	wrinklers	Wrinklers digesting now
 * @returns	{number}	Cookies
 */
function PopThreshold(wrinklers) {
  const respawn = WrinklerRespawnSeconds();
  if (!Number.isFinite(respawn)) return Infinity;
  const { plan, state } = AscensionCache;
  const remaining =
    plan && plan.applicable && Number.isFinite(plan.remaining)
      ? Math.max(plan.remaining, 0)
      : DEFAULT_REMAINING;
  const rho =
    plan && plan.applicable && plan.beta > 1 && state && state.runTime > 0
      ? (plan.beta - 1) / state.runTime
      : 0;
  const growth = Math.expm1(rho * remaining);
  if (!(growth > 0)) return Infinity;
  const lossPerSecond = (0.05 * (2 * wrinklers - 1) * 1.1 - 0.05) * Game.cookiesPs;
  return (lossPerSecond * respawn * (growth + 1)) / growth;
}

/**
 * Buys the next Grandmapocalypse research once it is unlocked and affordable, skipping the game's
 * confirmation prompt (buying with bypass is what its "Yes" button does)
 * @returns	{boolean}	Whether something was bought
 */
function BuyElderResearch() {
  for (let i = 0; i < ELDER_RESEARCH.length; i++) {
    const me = Game.Upgrades[ELDER_RESEARCH[i]];
    if (me && me.unlocked && !me.bought && Game.cookies >= me.getPrice()) {
      me.buy(1);
      return true;
    }
  }
  return false;
}

/**
 * "Elder nap", "Elder slumber" and "Elder calm": pledge, sign the covenant (which ends the pledge at
 * once), revoke it, and repeat until five pledges. With the Elder Pact the pledge comes back by itself
 * right away, so this takes seconds and a negligible amount of cookies instead of hours of peace
 * @returns	{boolean}	Whether something was bought
 */
function ElderAchievements() {
  if (Game.HasAchiev('Elder slumber') && Game.HasAchiev('Elder calm')) return false;
  if (!Game.Has('Elder Pact')) return false;
  const pledge = Game.Upgrades['Elder Pledge'];
  const covenant = Game.Upgrades['Elder Covenant'];
  const revoke = Game.Upgrades['Revoke Elder Covenant'];
  const affordable = (me) => me && me.unlocked && !me.bought && Game.cookies >= me.getPrice();
  if (covenant && covenant.bought) {
    if (affordable(revoke)) {
      revoke.buy(1);
      return true;
    }
    return false;
  }
  if (pledge && pledge.bought) {
    if (affordable(covenant)) {
      covenant.buy(1);
      return true;
    }
    return false;
  }
  if (affordable(pledge)) {
    pledge.buy(1);
    return true;
  }
  return false;
}

/**
 * Seconds of play left in this run, from the ascension planner
 * @returns	{number}
 */
function RunRemaining() {
  const { plan } = AscensionCache;
  return plan && plan.applicable && Number.isFinite(plan.remaining)
    ? Math.max(plan.remaining, 0)
    : DEFAULT_REMAINING;
}

/**
 * Long-run income in calm (a pledge holds: golden cookies, no wrinklers), in wrath with every wrinkler
 * kept, and in wrath with every wrinkler burst at once (a spree), refreshed every few seconds
 * @returns	{{calm: number, wrath: number, spree: number}}
 */
function StageIncomes() {
  if (!Stages || Date.now() - LastStageCheck > STAGE_CHECK_SECONDS * 1000) {
    LastStageCheck = Date.now();
    const income = (stage, W) => AutoplayEconomy(Game.cookies, 1, { stage, W }).income;
    Stages = {
      calm: income(0, 1),
      wrath: income(3, WrinklerFactor(Game.getWrinklersMax())),
      spree: income(3, 1),
    };
  }
  return Stages;
}

/**
 * How many wrinklers this run should burst for the next bursting achievement, if one is worth it: the
 * spree gives up the better stage's income for as long as the bursts take (every slot refills on its
 * own, so a burst comes every respawn time / slots), which must cost less than the achievement is
 * worth and fit in what is left of the run
 * @returns	{number}	Target count, 0 for none
 */
function SpreeTarget() {
  if (!Game.Has('Elder Pact')) return 0;
  const wait = (WrinklerRespawnSeconds(3) - CRAWL_SECONDS) / Math.max(Game.getWrinklersMax(), 1);
  if (!Number.isFinite(wait) || wait <= 0) return 0;
  const { calm, wrath, spree } = StageIncomes();
  const loss = 1 - spree / Math.max(calm, wrath);
  let from = Game.wrinklersPopped;
  for (let i = 0; i < SPREE_TARGETS.length; i++) {
    const [name, target] = SPREE_TARGETS[i];
    if (!Game.HasAchiev(name)) {
      const fits = (target - Game.wrinklersPopped) * wait <= RunRemaining();
      const cost = Math.max(target - from, 0) * wait * Math.max(loss, 0);
      return fits && cost <= AchievementWorth(1) ? target : 0;
    }
    from = Math.max(from, target);
  }
  return 0;
}

/**
 * Bursts every wrinkler as soon as it appears, except the one being poked for "Wrinkler poker"
 */
function Spree() {
  let spared = Game.HasAchiev('Wrinkler poker') ? null : PokeState.target;
  if (!Game.HasAchiev('Wrinkler poker') && !spared)
    spared = Game.wrinklers.find((me) => me.phase > 0 && me.type === 0) || null;
  for (let i = 0; i < Game.wrinklers.length; i++) {
    const me = Game.wrinklers[i];
    if (me.phase > 0 && me !== spared) me.hp = 0;
  }
}

/**
 * Revokes the Elder Covenant left by the elder achievements: it costs 5% of CpS for as long as it
 * holds, while a pledge holds the wrath off for free
 * @returns	{boolean}	Whether it revoked
 */
function RevokeCovenant() {
  const covenant = Game.Upgrades['Elder Covenant'];
  const revoke = Game.Upgrades['Revoke Elder Covenant'];
  if (!covenant || !covenant.bought || !revoke || !revoke.unlocked || revoke.bought) return false;
  if (Game.cookies < revoke.getPrice()) return false;
  revoke.buy(1);
  return true;
}

/**
 * Renews the Elder Pledge once it has run out (with the Elder Pact it unlocks again by itself)
 * @returns	{boolean}	Whether it pledged
 */
function Pledge() {
  const me = Game.Upgrades['Elder Pledge'];
  if (!me || !me.unlocked || me.bought || Game.cookies < me.getPrice()) return false;
  me.buy(1);
  return true;
}

/**
 * Pops the fattest normal wrinkler if it holds more than PopThreshold. Shiny wrinklers return three times
 * as much and are left for the ascension
 */
function PopWrinklers() {
  const digesting = Game.wrinklers.filter((me) => me.phase === 2);
  if (!digesting.length) return;
  const threshold = PopThreshold(digesting.length);
  let fattest = null;
  digesting.forEach((me) => {
    if (me.type === 0 && (fattest === null || me.sucked > fattest.sucked)) fattest = me;
  });
  if (fattest && fattest.sucked * 1.1 > threshold) fattest.hp = 0;
}

/**
 * Runs the Grandmapocalypse: research, the elder achievements (the wrath at its peak once, then
 * pledging, signing and revoking the covenant), bursting sprees, the choice of stage and wrinkler popping
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoElder() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoElder || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0)
    return;
  if (BuyElderResearch()) return;
  // "Grandmapocalypse" needs the wrath at its peak once, which it reaches a minute or two after the pact
  if (Game.Has('Elder Pact') && !Game.HasAchiev('Grandmapocalypse')) {
    PopWrinklers();
    return;
  }
  if (ElderAchievements()) return;
  if (RevokeCovenant()) return;
  if (SpreeTarget() > Game.wrinklersPopped) {
    Spree();
    return;
  }
  const { calm, wrath } = StageIncomes();
  if (Game.Has('Elder Pact') && calm > wrath && Pledge()) return;
  PopWrinklers();
}

;// ./src/Main/Autoplay/AutoGarden.js
/**
 * Section: the Garden under autoplay
 *
 * Breeding comes first. New seeds only come from mutations, which grow in empty tiles next to mature
 * plants of the right kinds (the game's mutation table), and each new seed brings the garden closer to
 * "Keeper of the conservatory" and to better plants: Thumbcorn (+2% click power, most of the income once
 * Godzamok multiplies clicks), Clover and Golden clover (golden cookies 1% and 3% more often). Autoplay
 * breeds along the chains whose parents can be planted: it plants the target's two parent kinds on a
 * checkerboard, so every empty tile touches both, uproots whatever else sprouts there (weeds, or more of
 * the parents), and lets a new kind grow up and picks it when mature, which unlocks its seed. Wood chips
 * (three mutation rolls a tick) or else fertilizer (a tick every 3 minutes) speed this up.
 *
 * With nothing left to breed, it plants the seed whose passive effect is worth most over its mature
 * life, keeping one tile free for mutations, on clay (effects x1.25). Plants are picked when mature, just
 * before they would die of old age (a mature harvest counts toward the harvest achievements). Effects
 * are valued with the auto-buyer's long-run income: +1% CpS raises everything that scales with CpS, +2%
 * click power the auto-clicker's (Godzamok-boosted) income, +1% golden cookie frequency the golden
 * cookie income.
 */




/** New seed, and the two parent kinds whose mature neighbours mutate an empty tile into it */
const BREEDING = [
  ['thumbcorn', 'bakerWheat', 'bakerWheat'],
  ['cronerice', 'bakerWheat', 'thumbcorn'],
  ['gildmillet', 'cronerice', 'thumbcorn'],
  ['clover', 'bakerWheat', 'gildmillet'],
  ['shimmerlily', 'clover', 'gildmillet'],
  ['elderwort', 'shimmerlily', 'cronerice'],
  ['goldenClover', 'bakerWheat', 'gildmillet'],
  ['bakeberry', 'bakerWheat', 'bakerWheat'],
  ['chocoroot', 'bakerWheat', 'brownMold'],
  ['whiteChocoroot', 'chocoroot', 'whiteMildew'],
  ['whiskerbloom', 'shimmerlily', 'whiteChocoroot'],
  ['chimerose', 'shimmerlily', 'whiskerbloom'],
  ['nursetulip', 'whiskerbloom', 'whiskerbloom'],
  ['tidygrass', 'bakerWheat', 'whiteChocoroot'],
  ['queenbeet', 'chocoroot', 'bakeberry'],
  ['duketater', 'queenbeet', 'queenbeet'],
];

/**
 * Share of long-run income a mature plant adds, for the seeds whose effect the model covers
 * @param	{string}	key	Seed key
 * @param	{object}	economy	From AutoplayEconomy()
 * @returns	{number}	Cookies per second
 */
function PlantValue(key, economy) {
  const cpsIncome = economy.cps * economy.growth.cps;
  const clickIncome = economy.clicks * economy.growth.click;
  if (['bakerWheat', 'bakeberry', 'chocoroot', 'whiteMildew'].includes(key))
    return 0.01 * cpsIncome;
  if (key === 'thumbcorn') return 0.02 * clickIncome;
  if (key === 'clover') return 0.01 * economy.golden;
  if (key === 'goldenClover') return 0.03 * economy.golden;
  if (key === 'shimmerlily') return 0.01 * economy.golden;
  if (key === 'drowsyfern') return 0.03 * cpsIncome - 0.05 * clickIncome - 0.1 * economy.golden;
  if (key === 'whiskerbloom') {
    // Milk 0.2% stronger: each kitten's factor 1 + k * milk * m grows with m
    const m = MilkMultiplier();
    const milk = Game.milkProgress || 0;
    let ratio = 1;
    [0.1, 0.125, 0.15, 0.175, 0.2, 0.2, 0.2, 0.2].forEach((k) => {
      ratio *= (1 + k * milk * m * 1.002) / (1 + k * milk * m);
    });
    return (ratio - 1) * cpsIncome;
  }
  return 0;
}

/**
 * Seconds a plant of this seed spends mature: it ages by ageTick + up to ageTickR per growth tick of the
 * soil, matures at `mature` and dies at 100
 * @param	{object}	me	Seed
 * @param	{number}	tickSeconds	Seconds per growth tick
 * @returns	{number}
 */
function MatureSeconds(me, tickSeconds) {
  const perTick = me.ageTick + me.ageTickR / 2;
  return me.immortal ? Infinity : (Math.max(100 - me.mature, 0) / perTick) * tickSeconds;
}

/**
 * The next seed to breed: the first in BREEDING still locked whose parents are both unlocked
 * @param	{object}	M	Garden minigame
 * @returns	{string[]|null}	[seed, parent, parent]
 */
function BreedingTarget(M) {
  return (
    BREEDING.find(
      ([seed, a, b]) =>
        M.plants[seed] &&
        !M.plants[seed].unlocked &&
        M.plants[a] &&
        M.plants[a].unlocked &&
        M.plants[b] &&
        M.plants[b].unlocked,
    ) || null
  );
}

/**
 * What a tile holds while breeding: on a checkerboard, parent tiles alternate between the two parent
 * kinds by column, so every empty tile has both among its neighbours ('' for an empty tile)
 * @param	{string[]}	target	[seed, parent, parent]
 * @param	{number}	x	Column
 * @param	{number}	y	Row
 * @returns	{string}	Seed key, or '' to keep empty
 */
function BreedingRole(target, x, y) {
  if ((x + y) % 2 !== 0) return '';
  return x % 2 === 0 ? target[1] : target[2];
}

/**
 * Switches the soil when the one wanted differs and the game allows it, as its button does
 * @param	{object}	M	Garden minigame
 * @param	{string[]}	wanted	Soil keys, best first
 * @returns	{boolean}	Whether it switched
 */
function ChooseSoil(M, wanted) {
  const soil = wanted.map((key) => M.soils[key]).find((me) => me && M.parent.amount >= me.req);
  if (!soil || soil.id === M.soil || M.nextSoil > Date.now()) return false;
  const button = l(`gardenSoil-${soil.id}`);
  if (!button) return false;
  button.click();
  return true;
}

/**
 * Plants a seed in an empty tile if the cookies not kept back for the "Lucky!" bank or a season cover it
 * @param	{object}	M	Garden minigame
 * @param	{object}	me	Seed
 * @param	{number}	x	Column
 * @param	{number}	y	Row
 * @returns	{boolean}	Whether it planted
 */
function Plant(M, me, x, y) {
  const { next } = AutoBuyState;
  if (!M.canPlant(me) || Game.cookies - (next ? next.reserve : 0) < M.getCost(me)) return false;
  return M.useTool(me.id, x, y);
}

/**
 * Tends the garden: breeds the next seed, or plants the best seed for its passive effect, and picks
 * plants while mature
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoGarden() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const farm = Game.Objects.Farm;
  if (!settings.AutoGarden || !farm.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0) return;
  const M = farm.minigame;
  if (!M || !M.plot || M.freeze) return;
  const tiles = [];
  for (let y = 0; y < 6; y++)
    for (let x = 0; x < 6; x++) if (M.isTileUnlocked(x, y)) tiles.push([x, y]);
  const target = BreedingTarget(M);
  if (ChooseSoil(M, target ? ['woodchips', 'fertilizer'] : ['clay'])) return;

  for (let i = 0; i < tiles.length; i++) {
    const [x, y] = tiles[i];
    const tile = M.plot[y][x];
    if (tile[0] >= 1) {
      const me = M.plantsById[tile[0] - 1];
      const mature = tile[1] >= me.mature;
      if (!me.unlocked) {
        // A new kind: let it grow up, and picking it then unlocks its seed
        if (mature) {
          M.harvest(x, y, 1);
          return;
        }
      } else if (target && BreedingRole(target, x, y) !== me.key) {
        // Anything else in a breeding tile, or the wrong kind in a parent tile, makes way
        M.harvest(x, y, 1);
        return;
      } else if (!me.immortal && mature && tile[1] + me.ageTick + me.ageTickR >= 100) {
        // Pick it while mature, just before the tick that could kill it
        M.harvest(x, y, 1);
        return;
      }
    }
  }

  const empty = tiles.filter(([x, y]) => M.plot[y][x][0] === 0);
  if (target) {
    for (let i = 0; i < empty.length; i++) {
      const [x, y] = empty[i];
      const role = BreedingRole(target, x, y);
      if (role && Plant(M, M.plants[role], x, y)) return;
    }
    return;
  }

  // Plant the best seed in every empty tile but the last one, kept free for mutations
  if (empty.length <= 1) return;
  const economy = AutoplayEconomy(Game.cookies);
  const tickSeconds = (M.soilsById[M.soil] ? M.soilsById[M.soil].tick : 5) * 60;
  let best = null;
  let bestGain = 0;
  M.plantsById.forEach((me) => {
    if (!me.unlocked || me.plantable === false || me.weed) return;
    const gain = PlantValue(me.key, economy) * MatureSeconds(me, tickSeconds) - M.getCost(me);
    if (gain > bestGain) {
      best = me;
      bestGain = gain;
    }
  });
  if (!best) return;
  // Planting competes with the auto-buyer: it must pay back faster (while mature) than the purchase the
  // buyer is saving for
  const { next } = AutoBuyState;
  if (next && M.getCost(best) / PlantValue(best.key, economy) > next.payback) return;
  Plant(M, best, empty[0][0], empty[0][1]);
}

;// ./src/Main/Autoplay/AutoGodzamok.js
/**
 * Section: Godzamok combos under autoplay
 *
 * Every frame with Godzamok slotted, sells and buys back each building type whose round trip pays (see
 * Cache/PP/Godzamok.js), within a few milliseconds, so the "Devastation" buff keeps growing for its ten
 * seconds and starts again when it runs out. The building counts are back where they were before the
 * frame ends, so CpS never changes and only click power needs recomputing.
 */




/** Below this many seconds left, let the buff run out and start a fresh one instead */
const MIN_SECONDS = 0.5;

let Next = 0;

/**
 * Sells and buys back building types round-robin until the frame's time budget is spent
 * It is called by Autoplay() every frame
 */
function AutoGodzamok() {
  if (Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0 || !DevastationBonus())
    return;
  const buff = Game.hasBuff('Devastation');
  const seconds = buff ? buff.time / Game.fps : BUFF_SECONDS;
  if (seconds < MIN_SECONDS) return;
  const clickIncome = (AutoClickRate() * Game.computedMouseCps) / (buff ? buff.multClick : 1);
  const types = CycleTypes(clickIncome, seconds, Game.cookies);
  if (!types.length) return;

  const { volume, buyMode, recalculateGains } = Game;
  Game.volume = 0; // no sale and purchase sounds
  Game.buyMode = 1; // in sell mode, buy() sells
  const start = performance.now();
  let units = 0;
  let intact = true;
  for (let pass = 0; pass < MAX_PASSES * types.length && intact; pass++) {
    if (pass > 0 && performance.now() - start >= BUDGET_MS) break;
    const me = types[Next % types.length];
    Next = (Next + 1) % types.length;
    const n = me.amount;
    me.sell(-1);
    me.buy(n);
    units += n;
    intact = me.amount === n;
  }
  const elapsed = performance.now() - start;
  if (units > 0) GodzamokState.msPerUnit = 0.9 * GodzamokState.msPerUnit + (0.1 * elapsed) / units;
  Game.volume = volume;
  Game.buyMode = buyMode;
  // Counts and CpS are unchanged, so skip the full recalculation (and Cookie Monster's resimulation that
  // follows it) unless a purchase fell short; the buff only changes click power
  Game.recalculateGains = intact ? recalculateGains : 1;
  Game.computedMouseCps = Game.mouseCps();
}

;// ./src/Main/Autoplay/AutoGolden.js
/** Frames of life left at which a golden cookie is clicked for "Fading luck" (it needs under a second) */
const FADING_LUCK_FRAMES = 20;

/**
 * Clicks golden cookies and reindeer as soon as they appear
 * Wrath cookies only show up during the Grandmapocalypse and are skipped if the setting says so. Until
 * "Fading luck" is won, golden cookies are clicked in their last second instead (it costs nothing: the
 * cookie's effect does not depend on when it is clicked)
 */
function AutoGolden() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (!settings.AutoGolden || Game.OnAscend || Game.AscendTimer > 0) return;
  const fading = settings.AutoAchievements && !Game.HasAchiev('Fading luck');
  Game.shimmers.slice().forEach((shimmer) => {
    if (shimmer.type === 'golden' && (!shimmer.wrath || settings.AutoGoldenWrath)) {
      if (!fading || shimmer.life <= FADING_LUCK_FRAMES) shimmer.pop();
    } else if (shimmer.type === 'reindeer') shimmer.pop();
  });
}

;// ./src/Main/Autoplay/AutoGrimoire.js
/**
 * Section: the Grimoire under autoplay
 *
 * Casts Force the Hand of Fate, a free golden cookie, whenever magic is full. Magic refills at a rate
 * proportional to sqrt(magic / max), faster the fuller the bar, so casting from the top of the bar uses
 * the fastest stretch of the refill: with about 70 magic a cast every 23 minutes, against 40 when casting
 * as soon as the cost is reached.
 */

/**
 * Casts Force the Hand of Fate when magic is full and no golden cookie is on screen (each one on screen
 * makes the spell 15% more likely to backfire)
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoGrimoire() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const tower = Game.Objects['Wizard tower'];
  if (!settings.AutoGrimoire || !tower.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0)
    return;
  const M = tower.minigame;
  const spell = M && M.spells['hand of fate'];
  if (!spell || Game.shimmerTypes.golden.n > 0) return;
  if (M.magic >= M.magicM - 0.5 && M.magic >= M.getSpellCost(spell)) M.castSpell(spell);
}

;// ./src/Main/Autoplay/AutoPantheon.js
/**
 * Section: the Pantheon under autoplay
 *
 * Tries every arrangement of the gods worth slotting, scores each by the long-run income the
 * auto-buyer uses (the game's own CpS and click power with those gods, plus golden cookies and
 * wrinklers), and moves gods into the best arrangement with the worship swaps a player would spend.
 */




/**
 * Gods worth trying. Godzamok is worth his "Devastation" buff, which autoplay keeps growing by selling
 * and buying back buildings (the economy counts its average). Holobore is only useful without auto
 * golden cookies (clicking one unslots it). Left out: Skruuia (turns every golden cookie into a wrath
 * cookie with extra clots and ruin, which the model does not cover; a pledge-free Grandmapocalypse does
 * the same for wrinklers), Cyclius (averages to nothing), Dotjeiess (weakens heavenly chips), Selebrak
 * and Rigidel (marginal)
 */
const CANDIDATES = ['ruin', 'mother', 'industry', 'labor', 'decadence', 'asceticism'];
/** How much less often golden cookies appear with Mokalsium and Jeremy in each slot */
const SLOWER = { mother: [1.15, 1.1, 1.05], industry: [1.1, 1.06, 1.03] };
/** Seconds between re-evaluations, and while a slot is empty (as after every ascension) */
const CHECK_SECONDS = 300;
const EMPTY_CHECK_SECONDS = 5;
/** Improvement in income needed to spend swaps on a new arrangement */
const MIN_GAIN = 0.01;
/**
 * Improvement worth a sugar lump to refill the swaps when they run short (from none, the next swap takes
 * 16 hours); Godzamok's buff alone multiplies income many times over
 */
const REFILL_GAIN = 0.5;

let LastCheck = 0;

/**
 * Factor on the golden cookie interval for an arrangement, relative to the gods slotted now
 * @param	{number[]}	slots	God ids per slot
 * @returns	{number}
 */
function IntervalFactor(slots) {
  const M = Game.Objects.Temple.minigame;
  let factor = 1;
  Object.keys(SLOWER).forEach((key) => {
    const slot = M.gods[key] ? slots.indexOf(M.gods[key].id) : -1;
    if (slot !== -1) factor *= SLOWER[key][slot];
  });
  return factor;
}

/**
 * Long-run income with the gods in the given slots: slots them, lets the game recompute CpS and click
 * power, scores the result and puts the original gods back
 * @param	{number[]}	slots	God ids per slot
 * @param	{number}	baseFactor	IntervalFactor of the current arrangement
 * @returns	{number}	Cookies per second
 */
function Score(slots, baseFactor) {
  const M = Game.Objects.Temple.minigame;
  const saved = M.slot.slice();
  const apply = (arrangement) => {
    Object.keys(M.godsById).forEach((id) => {
      M.godsById[id].slot = -1;
    });
    arrangement.forEach((id, slot) => {
      M.slot[slot] = id;
      if (id !== -1) M.godsById[id].slot = slot;
    });
  };
  apply(slots);
  Game.CalculateGains();
  const { income } = AutoplayEconomy(Game.cookies, IntervalFactor(slots) / baseFactor);
  apply(saved);
  Game.CalculateGains();
  return income;
}

/**
 * Moves gods into the given slots, one swap per god dropped into a slot (as dragging them would), and
 * moves their pictures in the Pantheon like a drop does
 * @param	{number[]}	slots	God ids per slot
 */
function Arrange(slots) {
  const M = Game.Objects.Temple.minigame;
  slots.forEach((id, slot) => {
    if (id === -1 || M.slot[slot] === id || M.swaps < 1) return;
    M.slotGod(M.godsById[id], slot);
    M.useSwap(1);
    M.lastSwapT = 0;
  });
  M.godsById.forEach((god) => {
    const div = l(`templeGod${god.id}`);
    const placeholder = l(`templeGodPlaceholder${god.id}`);
    if (!div || !placeholder) return;
    if (god.slot !== -1 && l(`templeSlot${god.slot}`)) {
      l(`templeSlot${god.slot}`).appendChild(div);
      placeholder.style.display = 'inline-block';
    } else {
      placeholder.parentNode.insertBefore(div, placeholder);
      placeholder.style.display = 'none';
    }
  });
}

/**
 * Refills the worship swaps with a sugar lump, accepting the game's prompt, as the Pantheon's refill
 * button does
 * @returns	{boolean}	Whether the swaps are full now
 */
function RefillSwaps() {
  const M = Game.Objects.Temple.minigame;
  if (Game.lumps < 1 || !Game.canRefillLump()) return false;
  Game.refillLump(1, () => {
    M.swaps = 3;
    M.swapT = Date.now();
  });
  ConfirmPrompt('SpendLump');
  return M.swaps >= 3;
}

/**
 * Slots the best gods once the Pantheon is unlocked, re-checking every few minutes, and refills the
 * worship swaps with a sugar lump when a much better arrangement waits for them
 * It is called by Autoplay() with the auto-buyer's cadence
 */
function AutoPantheon() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const temple = Game.Objects.Temple;
  if (!settings.AutoPantheon || !temple.minigameLoaded || Game.OnAscend || Game.AscendTimer > 0)
    return;
  const M = temple.minigame;
  if (!M) return;
  const soon = M.slot.includes(-1) || (LumpState.holdForSwaps && Game.lumps >= 1);
  if (Date.now() - LastCheck < (soon ? EMPTY_CHECK_SECONDS : CHECK_SECONDS) * 1000) return;
  LastCheck = Date.now();

  const ids = CANDIDATES.filter(
    (key) => M.gods[key] && (key !== 'asceticism' || !settings.AutoGolden),
  ).map((key) => M.gods[key].id);
  const baseFactor = IntervalFactor(M.slot);
  const current = Score(M.slot.slice(), baseFactor);
  let best = null;
  let bestIncome = current;
  ids.forEach((a) => {
    ids.forEach((b) => {
      ids.forEach((c) => {
        if (a === b || a === c || b === c) return;
        const income = Score([a, b, c], baseFactor);
        if (income > bestIncome) {
          best = [a, b, c];
          bestIncome = income;
        }
      });
    });
  });
  // Slots are filled diamond first; an empty slot is worth filling even when swaps run short
  const moves = best ? best.filter((id, slot) => M.slot[slot] !== id).length : 0;
  const filling = M.slot.includes(-1);
  const better = best !== null && bestIncome > current * (1 + MIN_GAIN);
  LumpState.holdForSwaps =
    better && !filling && M.swaps < moves && bestIncome > current * (1 + REFILL_GAIN);
  if (LumpState.holdForSwaps && RefillSwaps()) LumpState.holdForSwaps = false;
  if (better && (M.swaps >= moves || filling)) Arrange(best);
}

;// ./src/Main/Autoplay/Autoplay.js
















/** The other systems take turns on the frames between purchases */
const SYSTEMS = [
  AutoElder,
  AutoDragon,
  AutoSeasons,
  AutoLumps,
  AutoPantheon,
  AutoGrimoire,
  AutoGarden,
  AutoMarket,
  AutoAchievements,
];
/** Purchases are spaced by a few frames so Cookie Monster's caches catch up after each one */
const CYCLE_FRAMES = SYSTEMS.length + 1;

/**
 * Runs Cookie Monster+'s autoplay: clicking, golden cookies, Godzamok combos, purchases, the
 * Grandmapocalypse, the dragon, seasons, sugar lumps, the Pantheon, Grimoire, Garden and Stock Market,
 * easy achievements and ascensions
 * It is called every logic frame by CM.Main.Loop, including while ascending
 */
function Autoplay() {
  if (Game.T % Game.fps === 0) UpdateAutoClicker();
  AutoGolden();
  const turn = Game.T % CYCLE_FRAMES;
  if (ChallengeRun()) {
    // A Born again run has no minigames, lumps or seasons, and its rules forbid upgrades
    if (turn === 0) AutoBuy();
  } else {
    AutoGodzamok();
    if (turn === 0) AutoBuy();
    else SYSTEMS[turn - 1]();
  }
  AutoAscend();
}

;// ./src/Main/CheckStates/Garden.js



/**
 * This function checks if a garden tick has happened
 */
function CheckGardenTick() {
  if (
    Game.Objects.Farm.minigameLoaded &&
    LastGardenNextStep !== Game.Objects.Farm.minigame.nextStep
  ) {
    if (LastGardenNextStep !== 0 && LastGardenNextStep < Date.now()) {
      notificationsFunctions.createFlash('cookieMonsterMod', 3, 'GardFlash', false);
      notificationsFunctions.playCMSound(
        'cookieMonsterMod',
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GardSoundURL,
        'GardSound',
        'GardVolume',
        false,
      );
    }
    LastGardenNextStep = Game.Objects.Farm.minigame.nextStep;
  }
}

;// ./src/Disp/GoldenCookieTimers/GoldenCookieTimers.js
/** Section: Functions related to the Golden Cookie Timers */



/**
 * This function creates a new Golden Cookie Timer and appends it CM.Disp.GCTimers based on the id of the cookie
 * @param	{object}	cookie	A Golden Cookie object
 */
function CreateGCTimer(cookie) {
  const GCTimer = document.createElement('div');
  GCTimer.id = `GCTimer${cookie.id}`;
  GCTimer.style.width = '96px';
  GCTimer.style.height = '96px';
  GCTimer.style.position = 'absolute';
  GCTimer.style.zIndex = '10000000001';
  GCTimer.style.textAlign = 'center';
  GCTimer.style.lineHeight = '96px';
  GCTimer.style.fontFamily = '"Kavoon", Georgia, serif';
  GCTimer.style.fontSize = '35px';
  GCTimer.style.cursor = 'pointer';
  GCTimer.style.display = 'block';
  GCTimer.style.pointerEvents = 'none';
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GCTimer === 0)
    GCTimer.style.display = 'none';
  GCTimer.style.left = cookie.l.style.left;
  GCTimer.style.top = cookie.l.style.top;
  GCTimer.onclick = function () {
    cookie.pop();
  };
  GCTimer.onmouseover = function () {
    cookie.l.style.filter = 'brightness(125%) drop-shadow(0px 0px 3px rgba(255,255,255,1))'; // eslint-disable-line no-param-reassign
    cookie.l.style.webkitFilter = 'brightness(125%) drop-shadow(0px 0px 3px rgba(255,255,255,1))'; // eslint-disable-line no-param-reassign
  };
  GCTimer.onmouseout = function () {
    cookie.l.style.filter = ''; // eslint-disable-line no-param-reassign
    cookie.l.style.webkitFilter = ''; // eslint-disable-line no-param-reassign
  };

  GCTimers[cookie.id] = GCTimer;
  l('shimmers').appendChild(GCTimer);
}

;// ./src/Main/CheckStates/GoldenCookie.js








/**
 * Auxilirary function that finds all currently spawned shimmers.
 * CM.Cache.spawnedGoldenShimmer stores the non-user spawned cookie to later determine data for the favicon and tab-title
 * It is called by CM.CM.Main.CheckGoldenCookie
 */
function FindShimmer() {
  CurrSpawnedGoldenCookieState = 0;
  CacheGoldenShimmersByID = {};
  Object.keys(Game.shimmers).forEach((i) => {
    CacheGoldenShimmersByID[Game.shimmers[i].id] = Game.shimmers[i];
    if (Game.shimmers[i].spawnLead && Game.shimmers[i].type === 'golden') {
      CacheSpawnedGoldenShimmer = Game.shimmers[i];
      CurrSpawnedGoldenCookieState += 1;
    }
  });
}

/**
 * This function checks for changes in the amount of Golden Cookies
 * It is called by CM.Main.Loop
 */
function CheckGoldenCookie() {
  FindShimmer();
  Object.keys(GCTimers).forEach((i) => {
    if (typeof CacheGoldenShimmersByID[i] === 'undefined') {
      GCTimers[i].parentNode.removeChild(GCTimers[i]);
      delete GCTimers[i];
    }
  });
  if (LastGoldenCookieState !== Game.shimmerTypes.golden.n) {
    LastGoldenCookieState = Game.shimmerTypes.golden.n;
    if (LastGoldenCookieState) {
      if (LastSpawnedGoldenCookieState < CurrSpawnedGoldenCookieState) {
        // Autoplay pops golden cookies itself, so it needs no alerts
        if (!Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutoGolden) {
          notificationsFunctions.createFlash('cookieMonsterMod', 3, 'GCFlash', false);
          notificationsFunctions.playCMSound(
            'cookieMonsterMod',
            Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GCSoundURL,
            'GCSound',
            'GCVolume',
            false,
          );
          notificationsFunctions.createNotification(
            'cookieMonsterMod',
            'GCNotification',
            'Golden Cookie Spawned',
            'A Golden Cookie has spawned. Click it now!',
          );
        }
        // Reset the cumulative probability when a GC has spawned
        resetChanceTotal();
      }

      Object.keys(Game.shimmers).forEach((i) => {
        if (typeof GCTimers[Game.shimmers[i].id] === 'undefined') {
          CreateGCTimer(Game.shimmers[i]);
        }
      });
    }
    UpdateFavicon();
    LastSpawnedGoldenCookieState = CurrSpawnedGoldenCookieState;
    if (CurrSpawnedGoldenCookieState === 0) CacheSpawnedGoldenShimmer = 0;
  } else if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GCTimer === 1 &&
    LastGoldenCookieState
  ) {
    Object.keys(GCTimers).forEach((i) => {
      GCTimers[i].style.opacity = CacheGoldenShimmersByID[i].l.style.opacity;
      GCTimers[i].style.transform = CacheGoldenShimmersByID[i].l.style.transform;
      GCTimers[i].textContent = Math.ceil(CacheGoldenShimmersByID[i].life / Game.fps);
    });
  }
}

;// ./src/Main/CheckStates/Grimoire.js



/**
 * This function checks if the magic meter is full
 * It is called by CM.Main.Loop
 */
function CheckMagicMeter() {
  if (
    Game.Objects['Wizard tower'].minigameLoaded &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GrimoireBar === 1
  ) {
    const { minigame } = Game.Objects['Wizard tower'];
    if (minigame.magic < minigame.magicM) LastMagicBarFull = false;
    else if (!LastMagicBarFull) {
      LastMagicBarFull = true;
      notificationsFunctions.createFlash('cookieMonsterMod', 3, 'MagicFlash', false);
      notificationsFunctions.playCMSound(
        'cookieMonsterMod',
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.MagicSoundURL,
        'MagicSound',
        'MagicVolume',
        false,
      );
      notificationsFunctions.createNotification(
        'cookieMonsterMod',
        'MagicNotification',
        'Magic Meter full',
        'Your Magic Meter is full. Cast a spell!',
      );
    }
  }
}

;// ./src/Main/CheckStates/Season.js

 // eslint-disable-line no-unused-vars



/**
 * This function checks if there is reindeer that has spawned
 * It is called by CM.Main.Loop
 */
function CheckSeasonPopup() {
  if (LastSeasonPopupState !== Game.shimmerTypes.reindeer.spawned) {
    LastSeasonPopupState = Game.shimmerTypes.reindeer.spawned;
    Object.keys(Game.shimmers).forEach((i) => {
      if (Game.shimmers[i].spawnLead && Game.shimmers[i].type === 'reindeer') {
        CacheSeasonPopShimmer = Game.shimmers[i];
      }
    });
    notificationsFunctions.createFlash('cookieMonsterMod', 3, 'SeaFlash', false);
    notificationsFunctions.playCMSound(
      'cookieMonsterMod',
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SeaSoundURL,
      'SeaSound',
      'SeaVolume',
      false,
    );
    notificationsFunctions.createNotification(
      'cookieMonsterMod',
      'SeaNotification',
      'Reindeer sighted!',
      'A Reindeer has spawned. Click it now!',
    );
    // Reset the cumulative probability when a deer is spawned
    resetChanceTotalDeer();
  }
}

;// ./src/Main/CheckStates/Ticker.js



/**
 * This function checks if there is a fortune cookie on the ticker
 * It is called by CM.Main.Loop
 */
function CheckTickerFortune() {
  if (LastTickerFortuneState !== (Game.TickerEffect && Game.TickerEffect.type === 'fortune')) {
    LastTickerFortuneState = Game.TickerEffect && Game.TickerEffect.type === 'fortune';
    if (LastTickerFortuneState) {
      notificationsFunctions.createFlash('cookieMonsterMod', 3, 'FortuneFlash', false);
      notificationsFunctions.playCMSound(
        'cookieMonsterMod',
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.FortuneSoundURL,
        'FortuneSound',
        'FortuneVolume',
        false,
      );
      notificationsFunctions.createNotification(
        'cookieMonsterMod',
        'FortuneNotification',
        'Fortune Cookie found',
        'A Fortune Cookie has appeared on the Ticker.',
      );
    }
  }
}

;// ./src/Main/CheckStates/Wrinkler.js



/**
 * This function checks if any new Wrinklers have popped up
 * It is called by CM.Main.Loop
 */
function CheckWrinklerCount() {
  if (Game.elderWrath > 0) {
    let CurrentWrinklers = 0;
    Object.keys(Game.wrinklers).forEach((i) => {
      if (Game.wrinklers[i].phase === 2) CurrentWrinklers += 1;
    });
    if (CurrentWrinklers > LastWrinklerCount) {
      LastWrinklerCount = CurrentWrinklers;
      if (
        CurrentWrinklers === Game.getWrinklersMax() &&
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerMaxFlash
      ) {
        notificationsFunctions.createFlash('cookieMonsterMod', 3, 'WrinklerMaxFlash', false);
      } else {
        notificationsFunctions.createFlash('cookieMonsterMod', 3, 'WrinklerFlash', false);
      }
      if (
        CurrentWrinklers === Game.getWrinklersMax() &&
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerMaxSound
      ) {
        notificationsFunctions.playCMSound(
          'cookieMonsterMod',
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerMaxSoundURL,
          'WrinklerMaxSound',
          'WrinklerMaxVolume',
          false,
        );
      } else {
        notificationsFunctions.playCMSound(
          'cookieMonsterMod',
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerSoundURL,
          'WrinklerSound',
          'WrinklerVolume',
          false,
        );
      }
      if (
        CurrentWrinklers === Game.getWrinklersMax() &&
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.WrinklerMaxNotification
      ) {
        notificationsFunctions.createNotification(
          'cookieMonsterMod',
          'WrinklerMaxNotification',
          'Maximum Wrinklers Reached',
          'You have reached your maximum ammount of wrinklers',
        );
      } else {
        notificationsFunctions.createNotification(
          'cookieMonsterMod',
          'WrinklerNotification',
          'A Wrinkler appeared',
          'A new wrinkler has appeared',
        );
      }
    } else {
      LastWrinklerCount = CurrentWrinklers;
    }
  }
}

;// ./src/Main/LoopHook.js



























/**
 * Main loop of Cookie Monster
 * CM.init registers it to the "logic" hook provided by the modding api
 */
function CMLoopHook() {
  Autoplay();
  if (LastAscendState !== Game.OnAscend) {
    LastAscendState = Game.OnAscend;
    UpdateAscendState();
  }
  if (!Game.OnAscend && Game.AscendTimer === 0) {
    // Check if any other mods have been loaded
    if (LastModCount !== Object.keys(Game.mods).length) {
      InitData();
      InitCache();
      LastModCount = Object.keys(Game.mods).length;
    }

    // CM.Sim.DoSims is set whenever CPS has changed
    if (SimDoSims) {
      AllAmountTillNextAchievement(true);
      CacheIncome();

      CacheNoGoldSwitchCPS(); // Needed first
      CacheGoldenAndWrathCookiesMults();
      CacheStatsCookies();
      CacheAllMissingUpgrades();
      CacheChain();
      CacheDragonCost();
      CachePantheonGods();

      CacheSeasonSpec();
      CacheSellAllForChoEgg();

      SimDoSims = 0;
    }

    // Check for aura change to recalculate buildings prices
    const hasBuildAura = Game.auraMult('Fierce Hoarder') > 0;
    if (!CacheHadBuildAura && hasBuildAura) {
      CacheHadBuildAura = true;
      CacheDoRemakeBuildPrices = 1;
    } else if (CacheHadBuildAura && !hasBuildAura) {
      CacheHadBuildAura = false;
      CacheDoRemakeBuildPrices = 1;
    }

    if (CacheDoRemakeBuildPrices) {
      CacheBuildingsPrices();
      CacheDoRemakeBuildPrices = 0;
    }

    LoopCache();

    // Check all changing minigames and game-states
    CheckTickerFortune();
    CheckSeasonPopup();
    CheckGardenTick();
    CheckMagicMeter();
    CheckWrinklerCount();
    CheckAscensionReady();
  }
  // To remove Timers when ascending
  CheckGoldenCookie();
}

;// ./src/Data/headers.js
/** This includes all headers of Cookie Monster and their relevant data */
const headers_headers = {
  Favourite: 1,
  Calculation: 1,
  Notation: 1,
  Colours: 1,
  BarsDisplay: 1,
  Tooltip: 1,
  Statistics: 1,
  Notification: 1,
  NotificationGeneral: 1,
  NotificationGC: 1,
  NotificationFC: 1,
  NotificationSea: 1,
  NotificationGard: 1,
  NotificationMagi: 1,
  NotificationWrink: 1,
  NotificationWrinkMax: 1,
  NotificationAscend: 1,
  Autoplay: 1,
  Miscellaneous: 1,
  Ascension: 1,
  Lucky: 1,
  Chain: 1,
  Spells: 1,
  Garden: 1,
  Prestige: 1,
  Wrink: 1,
  Sea: 1,
  Achievs: 1,
  Misc: 1,
  infoMenu: 1,
  optionsMenu: 1,
};

/* harmony default export */ const Data_headers = (headers_headers);

;// ./src/InitSaveLoad/load.js









/**
 * This creates a load function to the CM object. Per Game code/comments:
 * "do stuff with the string data you saved previously"
 */
function load_load(str) {
  InitData();

  // Load saveData
  saveAndLoadingFunctions.loadMod('cookieMonsterMod', str, Data_settings, Data_headers, CMLoopHook);
  if (
    typeof Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames ===
    'undefined'
  ) {
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames = [];
  }

  // Update display with colours and locking of minigames
  UpdateColours();
  for (
    let index = 0;
    index < Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames.length;
    index++
  ) {
    const buildingIndex =
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.lockedMinigames[index];
    l(`row${buildingIndex}`).style.pointerEvents = 'none';
    l(`row${buildingIndex}`).style.opacity = '0.4';
    l(`productLock${buildingIndex}`).innerHTML = 'Unlock';
    l(`productLock${buildingIndex}`).style.pointerEvents = 'auto';
  }

  // Notify of update
  if (
    typeof Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.version !== 'undefined' &&
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.version !==
      `${VersionMajor}.${VersionMinor}`
  ) {
    if (Game.prefs.popups)
      Game.Popup(
        'A new version of Cookie Monster has been loaded, check out the release notes in the info tab!',
      );
    else
      Game.Notify(
        'A new version of Cookie Monster has been loaded, check out the release notes in the info tab!',
        '',
        '',
        0,
        1,
      );
  }
}

;// ./src/InitSaveLoad/init.js







/**
 * This creates a init function for the CM object. Per Game code/comments:
 * "this function is called as soon as the mod is registered
 * declare hooks here"
 * It starts the further initialization of CookieMonster and registers hooks
 */
function init_init() {
  // Load Cookie Monster Mod Framework and register mod
  initFunctions.initModFramework();
  window.cookieMonsterFrameworkData.isInitializing = true;
  initFunctions.registerMod('cookieMonsterMod');

  InitializeCookieMonster();
  Game.registerHook('click', CMClickHook);
  Game.registerHook('draw', CMDrawHook);
  Game.registerHook('logic', CMLoopHook);

  // Load default settings if no previous saveData is found
  if (typeof Game.modSaveData.cookieMonsterMod === 'undefined') {
    load_load('{}');
  }
}

;// ./src/InitSaveLoad/save.js


/**
 * This creates a save function to the CM object. Per Game code/comments:
 * "use this to store persistent data associated with your mod
 * return 'a string to be saved';"
 */
function save_save() {
  const saveObject = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  saveObject.version = `${VersionMajor}.${VersionMinor}`;
  return JSON.stringify(saveObject);
}

;// ./src/CookieMonster.js




const CM = {
  init: init_init,
  load: load_load,
  save: save_save,
  cookieMonsterPlus: true,
};

// Cookie Monster+ replaces the original mod: if the Workshop "Cookie Monster" is enabled as well,
// its registration (which happens later, after a network load) is skipped so only one copy runs
const { registerMod: CookieMonster_registerMod } = Game;
Game.registerMod = function (id, mod) {
  if (id === 'CookieMonster' && !mod.cookieMonsterPlus) {
    console.log('Cookie Monster+ is active, skipping the original Cookie Monster'); // eslint-disable-line no-console
    return false;
  }
  return CookieMonster_registerMod.apply(this, [id, mod]);
};

if (typeof Steam !== 'undefined') {
  // Need to add a delay for steam
  setTimeout(() => {
    Game.registerMod('CookieMonster', CM);

    // Game.registerMod also calls CM.load() which calls the loop hook
    // Thus sounds normally play at start up as Season and Garden states are checked
    window.cookieMonsterFrameworkData.isInitializing = false;
  }, 2000);
} else {
  Game.registerMod('CookieMonster', CM);
  window.cookieMonsterFrameworkData.isInitializing = false;
}

})();

/******/ })()
;