

class Gallery {

    constructor($el, coq) {
        this.$el = $el;
        this.coq = coq;
        this.pprint = coq.pprint;
        this.company_coq = coq.company_coq;
    }

    async showAll() {
        return this.show(ALL_JSON_URLS.slice().reverse());
    }

    async show(jsonUrls) {
        var data = await Promise.all(jsonUrls.map(
                async url => await (await fetch(url)).json())),
            waitFor = this.coq.when_ready || Promise.resolve();

        for (let goals of data) {
            let tr = $('<tr>').appendTo(this.$el);
            let hgoals = this.pprint.goals2DOM(goals);
            tr.append($('<td>').append(hgoals))
            this.company_coq.markup.applyToDOM(hgoals[0]);

            hgoals = this.pprint.goals2DOM(goals);
            tr.append($('<td>').append(hgoals))
            this.company_coq.markup.applyToDOM(hgoals[0]);
            //this.pprint.adjustBreaks(hgoals);
            waitFor.then(() => this.pprint.adjustBreaks(hgoals));
        }
    }
}

const ALL_JSON_URLS = [
        './gallery/01-remove_first_range.json',
        './gallery/02-remove_first_in.json',
        './gallery/03-remove_first_in-unfolded.json',
        './gallery/04-slf-triple-incr.json',
        './gallery/05-slf-triple-mlength.json',
    ];
