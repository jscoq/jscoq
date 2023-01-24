//@ts-check
"use strict";

// backend import
import { CoqWorker } from '../../../backend';

// frontend import
import $ from 'jquery';
import { FormatPrettyPrint } from '../../format-pprint/js';
import { CompanyCoq } from './addon/company-coq.js';

export class CoqContextualInfo {
    /**
     * @param {JQuery<HTMLElement>} container <div> element to show info in
     * @param {CoqWorker} coq jsCoq worker for querying types and definitions
     * @param {FormatPrettyPrint} pprint formatter for Pp data
     * @param {CompanyCoq} company_coq (optional) further beautification
     */
    constructor(container, coq, pprint, company_coq) {
        this.container = container;
        this.coq = coq;
        this.pprint = pprint;
        this.company_coq = company_coq;
        this.el = $('<div>').addClass('contextual-info').hide();
        this.content = $('<div>').addClass('content').appendTo(this.el);
        this.shadow = $('<div>').addClass(['scroll-shadow', 'scroll-shadow--bottom']).appendTo(this.el);

        this.is_visible = false;
        this.is_sticky = false;
        this.focus = null;
        this.minimal_exposure = Promise.resolve();

        this.MINIMAL_EXPOSURE_DURATION = 150; // ms

        this.container.append(this.el);

        // Set up mouse events
        var r = String.raw,
            sel = r`.constr\.reference, .constr\.variable, .constr\.type, .constr\.notation`;

        this.contextual_sel = sel;

        container.on('mouseenter', sel,  evt => this.onMouseEnter(evt));
        container.on('mousedown',  sel,  evt => this.onMouseDown(evt, true));
        container.on('mouseleave', sel,  evt => this.onMouseLeave(evt));
        container.on('mouseleave',       evt => this.onMouseLeave(evt));
        container.on('mousedown',        evt => this.hideReq());

        this.el.on('mouseenter',         evt => this.hideCancel());
        this.el.on('mousedown',          evt => { this.hideReq(); evt.stopPropagation(); });
        this.el.on('mouseover mouseout', evt => { evt.stopPropagation(); });

        // Need to bypass jQuery to set the passive flag for scroll event
        this.content[0].addEventListener('scroll', () => this.adjustScrollShadow(),
                                         {passive: true});

        this._keyHandler = this.keyHandler.bind(this);
        this._key_bound = false;
    }

    onMouseEnter(evt) { if (!this.is_sticky) this.showFor(evt.target, evt.altKey); }
    onMouseLeave(evt) { if (!this.is_sticky) this.hideReq(); }

    onMouseDown(evt)  {
        this.showFor(evt.target, evt.altKey);
        this.stick(evt.target);
        this.is_sticky = true;
        evt.stopPropagation();
    }

    showFor(dom, alt) {
        var jdom = $(dom), name = jdom.attr('data-name') || jdom.text();
        if (jdom.hasClass('constr.variable') ||
            jdom.hasClass('constr.type') || jdom.hasClass('constr.reference')) {
            if (alt) this.showPrint(name);
            else     this.showCheck(name, /*opaque*/false, /*silent_fail*/true);
        }
        else if (jdom.hasClass('constr.notation')) {
            this.showLocate(name);
        }
    }

    showCheck(name, opaque=false, silent_fail=false) {
        this.focus = {identifier: name, info: 'Check', opaque};
        this.showQuery(`Check ${name}.`, silent_fail ? null : this.formatName(name));
    }

    showChecks(names, opaque=false, silent_fail=false) {
        this.focus = {identifier: names[0], info: 'Check', opaque};  /** @todo */
        this.showQueries(names.map(name =>
            [`Check ${name}.`, silent_fail ? null : this.formatName(name)]));
    }

    showAbouts(names, opaque=false, silent_fail=false) {
        this.focus = {identifier: names[0], info: 'About', opaque};  /** @todo */
        this.showQueries(names.map(name =>
            [`About ${name}.`, silent_fail ? null : this.formatName(name)]));
    }

    showPrint(name) {
        this.focus = {identifier: name, info: 'Print'};
        this.showQuery(`Print ${name}.`, this.formatName(name));
    }

    showLocate(symbol) {
        this.focus = {symbol: symbol, info: 'Locate'};
        this.showQuery(`Locate "${symbol}".`, `"${symbol}"`);
    }

    async showQuery(command, title) {
        this.is_visible = true;
        var msg = await this._query(command, title);
        if (msg && this.is_visible)
            this.show(msg.pp);
    }

    async showQueries(queryArgs /* [command, title][] */) {
        this.is_visible = true;
        var msgs = (await Promise.all(queryArgs.map(
            ([command, title]) => this._query(command, title))))
            .filter(x => x);

        // If there are more than 2 n/a, summarize them (to prevent a long useless list)
        var na = msgs.filter(x => x.status === 'na');
        if (msgs.some(x => x.status === 'ok') && na.length > 2) {
            msgs = msgs.filter(x => x.status !== 'na')
                .concat([{
                    pp: this.formatText('...', `(+ ${na.length} unavailable symbols)`),
                    status: 'na'
                }]);
        }
        // sort messages by tag length (shortest match first)
        // penalize n/a results so that they appear last
        msgs = this._sortBy(msgs,
                            x => (x.pp.attr('tag') || '').length +
                                 (x.status === 'na' ? 1000 : 0));
        if (msgs.length > 0 && this.is_visible)
            this.show(msgs.map(({pp}) => pp));
    }

    async _query(command, title) {
        try {
            var result = await this.coq.queryPromise(0, ['Vernac', command]);
            return {pp: this.formatMessages(result), status: 'ok'}
        }
        catch (err) {
            if (title)
                return {pp: this.formatText(title, "(not available)"), status: 'na'};
        }
    }

    show(html) {
        this.content.html(html);
        this.el.show();
        this.is_visible = true;
        this.minimal_exposure = this.elapse(this.MINIMAL_EXPOSURE_DURATION);
        if (!this._key_bound) {
            this._key_bound = true;
            $(document).on('keydown keyup', this._keyHandler);
        }
        requestAnimationFrame(() => this.adjustScrollShadow());
    }

    hide() {
        this.unstick();
        this.el.hide();
        this.is_visible = false;
        this.is_sticky = false;
        $(document).off('keydown keyup', this._keyHandler);
        this._key_bound = false;
    }

    hideReq() {
        this.request_hide = true;
        this.minimal_exposure.then(() => { if (this.request_hide) this.hide() });
    }

    hideCancel() {
        this.request_hide = false;
    }

    stick(dom) {
        this.unstick();
        $(dom).addClass('contextual-focus');
    }

    unstick() {
        this.container.find('.contextual-focus').removeClass('contextual-focus');
    }

    /**
     * Provides a visual cue that there's more content to be had by scrolling.
     */
    adjustScrollShadow() {
        var amount = this.content[0].scrollHeight - this.content[0].offsetHeight,
            at = this.content[0].scrollTop;
        this.shadow.css({opacity: Math.max(0, Math.min(100, amount - at)) / 100});
    }

    /**
     * Stores current identifier names, esp. before
     * prettifying text with company-coq.
     */
    pinIdentifiers(jdom) {
        if (!jdom) jdom = this.container;
        for (let el of jdom.find(this.contextual_sel)) {
            $(el).attr('data-name', $(el).text());
        }
    }

    keyHandler(evt) {
        var name = this.focus && this.focus.identifier;
        if (name && !this.focus.opaque) {
            if (evt.altKey) this.showPrint(name);
            else            this.showCheck(name);
        }
    }

    formatMessages(msgs) {
        var ppmsgs = msgs.map(feedback => this.pprint.msg2DOM(feedback.msg)),
            frag = $(document.createDocumentFragment());

        for (let e of ppmsgs) {
            frag.append($('<div>').append(e));
        }

        if (this.company_coq) {
            this.company_coq.markup.applyToDOM(frag[0]);
        }

        if (msgs[0] && msgs[0].msg)
            frag.attr('tag', this.getFirstLine(msgs[0].msg));

        return frag;
    }

    formatName(name) {
        var comps = name.split('.'),
            span = $('<span>');
        for (let path_el of comps.slice(0, comps.length - 1)) {
            span.append($('<span>').addClass('constr.path').text(path_el));
            span.append(document.createTextNode('.'));
        }
        span.append($('<span>').addClass('constr.reference').text(comps.last()));
        return span;
    }

    formatText(title, msg) {
        return $('<div>')
            .append(typeof title === 'string' ? $('<span>').text(title) : title)
            .append($('<br/>'))
            .append($('<span>').addClass('message').text("  " + msg));
    }

    getFirstLine(msg) {
        var txt = this.pprint.pp2Text(msg);
        return txt.match(/^[^\n]*/)[0];
    }

    elapse(duration) {
        return new Promise((resolve, reject) =>
            setTimeout(resolve, duration));
    }

    _sortBy(arr, f) {
        let cmp = (x, y) => { /* note: this routine puts falsey values at the end */
            let fx = f(x), fy = f(y);
            return (fx && (!fy || fx < fy)) ? -1
                 : (fy && (!fx || fy < fx)) ? 1 : 0;
        };
        return arr.sort(cmp);
    }
}
