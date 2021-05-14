
class SettingsPanel {
    html() {
        return `
        <div class="settings-panel">
            <div>
                <label for="settings--theme">
                    <div class="setting">
                        Light switch</label>
                        <input id="settings--theme" type="checkbox" class="switch">
                    </div>
                </label>
                <label for="settings--company">
                    <div class="setting">
                        Enable company-coq
                        <input id="settings--company" type="checkbox" class="switch">
                    </div>
                </label>
            </div>
            <div class="links">
                <a href="https://coq.zulipchat.com/#narrow/stream/256336-jsCoq" title="Zulip" class="link-to-zulip"></a>
                <a href="https://github.com/jscoq/jscoq" title="GitHub" class="link-to-github"></a>
            </div>
        </div>
        `;
    }

    constructor() {
        this.el = $(this.html());
    }

    show() {
        $(document.body).append(this.el);
    }

    hide() {
        this.el.remove();
    }

    toggle() {
        if (this.isShown()) this.hide();
        else this.show();
        return this.isShown();
    }

    isShown() {
        return this.el.parent().length > 0;
    }
}